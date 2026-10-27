# PC Remote Wi-Fi : serveur pour Windows (Python 3, aucune dépendance à installer)
import uuid, array, base64, ctypes, hashlib, io, json, math, os, platform, queue, random, shutil, socket, struct, sys, threading, time, urllib.request, webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

PORT = 8080
PIN_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "pin.txt")


def load_pin():
    """PIN stable : memorise dans pin.txt (supprime ce fichier pour en generer un nouveau)."""
    try:
        p = open(PIN_FILE).read().strip()
        if p.isdigit() and len(p) in (4, 6):
            return p
    except Exception:
        pass
    p = "%06d" % random.SystemRandom().randint(0, 999999)
    try:
        open(PIN_FILE, "w").write(p)
    except Exception:
        pass
    return p


PIN = load_pin()

VERSION = "v18"
BUILD = 18
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
UPDATE_FILE = os.path.join(BASE_DIR, "update_url.txt")
RESTART_FLAG = os.path.join(BASE_DIR, "restart.flag")
RESTARTED = os.path.exists(RESTART_FLAG)
if RESTARTED:
    try:
        os.remove(RESTART_FLAG)
    except Exception:
        pass
IS_WIN = platform.system() == "Windows"

MODS = {"ctrl": 0x11, "alt": 0x12, "shift": 0x10, "win": 0x5B}
EXTENDED = {0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x2D, 0x2E, 0x5B, 0x5C}
BTN = {"l": (0x0002, 0x0004), "r": (0x0008, 0x0010), "m": (0x0020, 0x0040)}

if IS_WIN:
    from ctypes import wintypes
    ULONG_PTR = ctypes.c_size_t

    class MOUSEINPUT(ctypes.Structure):
        _fields_ = [("dx", wintypes.LONG), ("dy", wintypes.LONG), ("mouseData", wintypes.DWORD),
                    ("dwFlags", wintypes.DWORD), ("time", wintypes.DWORD), ("dwExtraInfo", ULONG_PTR)]

    class KEYBDINPUT(ctypes.Structure):
        _fields_ = [("wVk", wintypes.WORD), ("wScan", wintypes.WORD), ("dwFlags", wintypes.DWORD),
                    ("time", wintypes.DWORD), ("dwExtraInfo", ULONG_PTR)]

    class _U(ctypes.Union):
        _fields_ = [("mi", MOUSEINPUT), ("ki", KEYBDINPUT)]

    class INPUT(ctypes.Structure):
        _anonymous_ = ("u",)
        _fields_ = [("type", wintypes.DWORD), ("u", _U)]

    user32 = ctypes.windll.user32
    user32.SendInput.argtypes = (wintypes.UINT, ctypes.POINTER(INPUT), ctypes.c_int)

    def _send(inputs):
        if not inputs:
            return
        arr = (INPUT * len(inputs))(*inputs)
        user32.SendInput(len(inputs), arr, ctypes.sizeof(INPUT))

    def _mouse(flags, dx=0, dy=0, data=0):
        i = INPUT(type=0)
        i.mi = MOUSEINPUT(dx, dy, data & 0xFFFFFFFF, flags, 0, 0)
        return i

    def _key(vk=0, scan=0, flags=0):
        i = INPUT(type=1)
        i.ki = KEYBDINPUT(vk, scan, flags, 0, 0)
        return i
else:
    def _send(inputs):  # mode test hors Windows
        print("[test]", inputs)

    def _mouse(flags, dx=0, dy=0, data=0):
        return ("mouse", flags, dx, dy, data)

    def _key(vk=0, scan=0, flags=0):
        return ("key", vk, scan, flags)


def move(dx, dy):
    _send([_mouse(0x0001, int(dx), int(dy))])


def absmove(x, y):
    x = max(0.0, min(1.0, float(x)))
    y = max(0.0, min(1.0, float(y)))
    _send([_mouse(0x8001, int(x * 65535), int(y * 65535))])


def wheel(n):
    _send([_mouse(0x0800, 0, 0, int(n) * 120)])


def button(b, down):
    if b in BTN:
        _send([_mouse(BTN[b][0] if down else BTN[b][1])])


def press(vk, mods=()):
    mvk = [MODS[m] for m in mods if m in MODS]
    seq = [_key(m, 0, 1 if m == 0x5B else 0) for m in mvk]
    ext = 0x0001 if vk in EXTENDED else 0
    seq.append(_key(vk, 0, ext))
    seq.append(_key(vk, 0, ext | 0x0002))
    seq += [_key(m, 0, (1 if m == 0x5B else 0) | 0x0002) for m in reversed(mvk)]
    _send(seq)


def text(s, mods=()):
    if mods and len(s) == 1 and s.isalnum() and s.isascii():
        return press(ord(s.upper()), mods)
    for ch in s:
        if ch == "\n":
            press(0x0D)
        elif ch == "\t":
            press(0x09)
        else:
            data = ch.encode("utf-16-le")
            for k in range(0, len(data), 2):
                unit = data[k] | (data[k + 1] << 8)
                _send([_key(0, unit, 0x0004), _key(0, unit, 0x0004 | 0x0002)])


def handle(events):
    for e in events:
        t = e.get("t")
        if t == "m":
            move(e["x"], e["y"])
        elif t == "s":
            wheel(e["n"])
        elif t == "a":
            absmove(e["x"], e["y"])
        elif t == "c":
            button(e["b"], True); button(e["b"], False)
        elif t == "d":
            button(e["b"], True)
        elif t == "u":
            button(e["b"], False)
        elif t == "k":
            press(int(e["vk"]), e.get("mods", []))
        elif t == "txt":
            text(e["s"], e.get("mods", []))


class AudioHub:
    """Capture le son du PC (WASAPI loopback) et le diffuse aux clients connectes."""

    def __init__(self):
        self.lock = threading.Lock()
        self.subs = []
        self.rate = 48000
        self.ch = 2
        self.p = None
        self.stream = None
        self.stop_evt = None
        self.watch_evt = None
        self.out_name = None

    def _watch(self, evt):
        """Relance la capture si le PC sort de veille ou si la sortie audio change (casque, HDMI...)."""
        while not evt.wait(3):
            try:
                bad = False
                st = self.stream
                if st is not None and not st.is_active():
                    bad = True
                else:
                    import pyaudiowpatch as pa
                    q = pa.PyAudio()
                    try:
                        w = q.get_host_api_info_by_type(pa.paWASAPI)
                        cur = q.get_device_info_by_index(w["defaultOutputDevice"])["name"]
                    finally:
                        q.terminate()
                    if self.out_name and cur != self.out_name:
                        bad = True
                if not bad:
                    continue
                with self.lock:
                    if evt.is_set() or not self.subs:
                        return
                    print("Audio : sortie changee ou PC reveille, redemarrage de la capture...")
                    self._stop()
                    try:
                        self._start()
                        return  # _start a lance un nouveau veilleur
                    except Exception as ex:
                        print("Audio : redemarrage impossible (%s), nouvel essai dans 3 s" % ex)
                        evt = self.watch_evt = threading.Event()
            except Exception as ex:
                print("audio veilleur :", ex)

    def subscribe(self, maxsize=40):
        with self.lock:
            if not self.subs:
                self._start()
            q = queue.Queue(maxsize=maxsize)
            self.subs.append(q)
            return q, self.rate, self.ch

    def unsubscribe(self, q):
        with self.lock:
            if q in self.subs:
                self.subs.remove(q)
            if not self.subs:
                self._stop()

    def _push(self, data):
        for q in list(self.subs):
            try:
                q.put_nowait(data)
            except queue.Full:
                try:
                    q.get_nowait()
                    q.put_nowait(data)
                except Exception:
                    pass

    def _start(self):
        if not IS_WIN:  # mode test : un la a 440 Hz
            self.rate, self.ch = 48000, 2
            self.stop_evt = threading.Event()
            evt = self.stop_evt

            def gen():
                n = 0
                step = 480
                while not evt.is_set():
                    buf = bytearray()
                    for i in range(step):
                        v = int(8000 * math.sin(2 * math.pi * 440 * (n + i) / 48000))
                        buf += struct.pack("<hh", v, v)
                    n += step
                    self._push(bytes(buf))
                    time.sleep(0.01)
            threading.Thread(target=gen, daemon=True).start()
            return
        try:
            import pyaudiowpatch as pyaudio
        except ImportError:
            raise RuntimeError("PyAudioWPatch n'est pas installe : ferme et relance lancer.bat")
        p = None
        try:
            p = pyaudio.PyAudio()
            wasapi = p.get_host_api_info_by_type(pyaudio.paWASAPI)
            dev = p.get_device_info_by_index(wasapi["defaultOutputDevice"])
            self.out_name = dev["name"]
            if not dev.get("isLoopbackDevice"):
                for lb in p.get_loopback_device_info_generator():
                    if dev["name"] in lb["name"]:
                        dev = lb
                        break
            self.rate = int(dev["defaultSampleRate"])
            src_ch = int(dev["maxInputChannels"])
            self.ch = 2  # tout est mixe en stereo avant diffusion

            def cb(in_data, frame_count, time_info, status):
                self._push(in_data if src_ch == 2 else to_stereo(in_data, src_ch))
                return (None, pyaudio.paContinue)

            self.stream = p.open(format=pyaudio.paInt16, channels=src_ch, rate=self.rate,
                                 frames_per_buffer=480, input=True,
                                 input_device_index=dev["index"], stream_callback=cb)
            self.p = p
            self.watch_evt = threading.Event()
            threading.Thread(target=self._watch, args=(self.watch_evt,), daemon=True).start()
            print("Audio : capture de '%s' (%d Hz, %d canaux -> stereo)" % (dev["name"], self.rate, src_ch))
        except Exception as ex:
            try:
                if p is not None:
                    p.terminate()  # libere le peripherique audio en cas d'echec
            except Exception:
                pass
            raise RuntimeError("Aucune sortie audio utilisable dans Windows (%s). "
                               "Verifie Parametres > Systeme > Son > Sortie." % ex)

    def _stop(self):
        if self.watch_evt:
            self.watch_evt.set()
            self.watch_evt = None
        if self.stop_evt:
            self.stop_evt.set()
            self.stop_evt = None
        try:
            if self.stream:
                self.stream.stop_stream()
                self.stream.close()
            if self.p:
                self.p.terminate()
        except Exception:
            pass
        self.stream = None
        self.p = None


HUB = AudioHub()


# Poids (gauche, droite) par canal, ordre WASAPI usuel : 5.1 = FL FR FC LFE BL BR, 7.1 = FL FR FC LFE BL BR SL SR
DOWNMIX = {
    3: ([1, 0, .707], [0, 1, .707]),
    4: ([1, 0, .707, 0], [0, 1, 0, .707]),
    5: ([1, 0, .707, .5, 0], [0, 1, .707, 0, .5]),
    6: ([1, 0, .707, 0, .5, 0], [0, 1, .707, 0, 0, .5]),
    8: ([1, 0, .707, 0, .5, 0, .5, 0], [0, 1, .707, 0, 0, .5, 0, .5]),
}
DOWNMIX_GAIN = 0.7  # evite la saturation quand plusieurs canaux s'additionnent
_DM_MATRIX = {}


def to_stereo(data, ch):
    """Convertit des echantillons 16 bits a ch canaux en stereo (avec canal central et arrieres)."""
    if ch == 2:
        return data
    try:
        import numpy as np
    except Exception:
        np = None
    if np is not None:
        a = np.frombuffer(data, dtype=np.int16)
        n = len(a) // ch
        a = a[:n * ch].reshape(n, ch).astype(np.float32)
        if ch == 1:
            return np.repeat(a, 2, axis=1).astype("<i2").tobytes()
        m = _DM_MATRIX.get(ch)
        if m is None:
            w = DOWNMIX.get(ch)
            if w:
                m = np.array(w, dtype=np.float32).T * DOWNMIX_GAIN
                m[0, 0] = m[1, 1] = 1.0  # les avants gauche/droite restent a pleine puissance
            else:
                m = np.zeros((ch, 2), dtype=np.float32)
                m[0, 0] = m[1, 1] = 1.0
            _DM_MATRIX[ch] = m
        return np.clip(a @ m, -32768, 32767).astype("<i2").tobytes()
    a = array.array("h")
    a.frombytes(data)
    n = len(a) // ch
    a = a[:n * ch]
    out = array.array("h", bytes(4 * n))
    if ch == 1:
        out[0::2] = a[0::1]
        out[1::2] = a[0::1]
        return out.tobytes()
    w = DOWNMIX.get(ch)
    if not w:
        out[0::2] = a[0::ch]
        out[1::2] = a[1::ch]
        return out.tobytes()
    wl = [(c, 1.0 if c == 0 else w[0][c] * DOWNMIX_GAIN) for c in range(ch) if w[0][c]]
    wr = [(c, 1.0 if c == 1 else w[1][c] * DOWNMIX_GAIN) for c in range(ch) if w[1][c]]
    for k in range(n):
        base = k * ch
        l = int(sum(a[base + c] * x for c, x in wl))
        r = int(sum(a[base + c] * x for c, x in wr))
        out[2 * k] = -32768 if l < -32768 else 32767 if l > 32767 else l
        out[2 * k + 1] = -32768 if r < -32768 else 32767 if r > 32767 else r
    return out.tobytes()


class ScreenHub:
    """Capture l'ecran principal en JPEG (~15 images/s) tant qu'au moins un client regarde."""

    def __init__(self):
        self.cond = threading.Condition()
        self.viewers = 0
        self.lite = 0
        self.frame = None
        self.seq = 0
        self.running = False

    def add(self, lite=False):
        with self.cond:
            self.viewers += 1
            if lite:
                self.lite += 1
            if not self.running:
                self.running = True
                threading.Thread(target=self._loop, daemon=True).start()

    def remove(self, lite=False):
        with self.cond:
            self.viewers -= 1
            if lite:
                self.lite -= 1

    def wait(self, last):
        with self.cond:
            self.cond.wait_for(lambda: self.seq != last, timeout=2)
            return self.frame, self.seq

    def _capture(self):
        from PIL import Image, ImageDraw
        if IS_WIN:
            from PIL import ImageGrab
            im = ImageGrab.grab().convert("RGB")
            pt = wintypes.POINT()
            user32.GetCursorPos(ctypes.byref(pt))
            cx, cy = pt.x, pt.y
        else:  # mode test
            im = Image.new("RGB", (1920, 1080), (30, 60, 120))
            ImageDraw.Draw(im).text((100, 100), "TEST %.2f" % time.time(), fill=(255, 255, 255))
            cx, cy = 500, 400
        s = max(1.0, im.width / 1280.0)
        d = ImageDraw.Draw(im)
        pts = [(0, 0), (0, 22), (6, 17), (11, 28), (15, 26), (10, 16), (17, 16)]
        d.polygon([(cx + x * s, cy + y * s) for x, y in pts], fill=(255, 255, 255), outline=(0, 0, 0))
        lite = self.lite > 0  # economie de donnees (4G/5G, acces a distance)
        im.thumbnail((800, 800) if lite else (1280, 1280))
        buf = io.BytesIO()
        im.save(buf, "JPEG", quality=38 if lite else 60)
        return buf.getvalue()

    def _loop(self):
        last_err = None
        while True:
            with self.cond:
                if self.viewers <= 0:
                    self.running = False
                    return
            t = time.time()
            try:
                jpg = self._capture()
                with self.cond:
                    self.frame = jpg
                    self.seq += 1
                    self.cond.notify_all()
            except Exception as ex:
                if str(ex) != last_err:
                    print("ecran :", ex)
                    last_err = str(ex)
                time.sleep(1)
            time.sleep(max(0.0, (0.15 if self.lite > 0 else 0.04) - (time.time() - t)))


SCREEN = ScreenHub()


# ---------------- Mises a jour automatiques ----------------
def valid_update_url(u):
    return u.startswith("https://") or u.startswith("http://127.0.0.1") or u.startswith("http://localhost")


DEFAULT_UPDATE_URL = "https://raw.githubusercontent.com/zonesafe/Pcremote/main"


def update_base():
    try:
        u = open(UPDATE_FILE, encoding="utf-8").read().strip().splitlines()[0].strip().rstrip("/")
    except Exception:
        u = DEFAULT_UPDATE_URL
    return u if valid_update_url(u) else None


def http_get(url, timeout=10):
    req = urllib.request.Request(url, headers={"User-Agent": "PCRemote-updater", "Cache-Control": "no-cache"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


UPDATE_LOCK = threading.Lock()


def check_update():
    base = update_base()
    if not base:
        return "Mises a jour automatiques non configurees : colle l'adresse des mises a jour ci-dessus."
    with UPDATE_LOCK:
        try:
            meta = json.loads(http_get(base + "/version.json?t=%d" % int(time.time())).decode("utf-8"))
            build = int(meta["build"])
        except Exception as ex:
            return "Impossible de verifier les mises a jour : %s" % ex
        if build <= BUILD:
            return "A jour (%s)" % VERSION
        try:
            code = http_get(base + "/server.py?t=%d" % int(time.time()), 30)
            if hashlib.sha256(code).hexdigest() != str(meta.get("sha256", "")).lower():
                return "Fichier recu invalide (empreinte differente) : mise a jour ignoree"
            compile(code, "server.py", "exec")
        except Exception as ex:
            return "Echec du telechargement de la mise a jour : %s" % ex
        path = os.path.abspath(__file__)
        try:
            shutil.copyfile(path, path + ".prev")  # sauvegarde de l'ancienne version
            tmp = path + ".new"
            with open(tmp, "wb") as f:
                f.write(code)
            os.replace(tmp, path)
            with open(RESTART_FLAG, "w") as f:
                f.write("1")
        except Exception as ex:
            return "Echec de l'installation : %s" % ex
        threading.Timer(0.8, lambda: os._exit(3)).start()  # lancer.bat relance le serveur
        return "Mise a jour %s installee, redemarrage..." % meta.get("version", build)


def update_api(req):
    if req.get("action") == "set":
        u = str(req.get("url", "")).strip().rstrip("/")
        if not valid_update_url(u):
            return "Adresse refusee : elle doit commencer par https://"
        with open(UPDATE_FILE, "w", encoding="utf-8") as f:
            f.write(u + "\n")
        return "Adresse enregistree. " + check_update()
    return check_update()


def updater_loop():
    time.sleep(5)
    while True:
        if update_base():
            msg = check_update()
            if not msg.startswith("A jour"):
                print("[maj]", msg)
        time.sleep(60)


def ws_frame(op, payload):
    n = len(payload)
    if n < 126:
        h = struct.pack("!BB", 0x80 | op, n)
    elif n < 65536:
        h = struct.pack("!BBH", 0x80 | op, 126, n)
    else:
        h = struct.pack("!BBQ", 0x80 | op, 127, n)
    return h + payload


FAILS = {}
FAIL_LOCK = threading.Lock()


class H(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def handle(self):
        try:
            super().handle()
        except (ConnectionError, TimeoutError):
            pass  # le telephone a ferme la connexion : normal

    def setup(self):
        super().setup()
        try:
            self.connection.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)  # pas d'attente d'Nagle
        except Exception:
            pass

    def log_message(self, *a):
        pass

    def _reply(self, code, body=b"", ctype="text/plain; charset=utf-8", cache=False):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "public, max-age=604800" if cache else "no-store")
        self.end_headers()
        self.wfile.write(body)

    def _auth(self, supplied):
        """Verifie le PIN. 5 erreurs de suite depuis une meme adresse = blocage 60 s."""
        ip = self.client_address[0]
        now = time.time()
        locked = False
        ok = False
        with FAIL_LOCK:
            n, until = FAILS.get(ip, (0, 0.0))
            if until > now:
                locked = True
            elif supplied == PIN:
                FAILS.pop(ip, None)
                ok = True
            else:
                n += 1
                if n >= 5:
                    FAILS[ip] = (0, now + 60)
                    print("[securite] trop d'essais de PIN depuis %s : bloque 60 s" % ip)
                else:
                    FAILS[ip] = (n, 0.0)
        if ok:
            return True
        if locked:
            self._reply(429, "Trop d'essais : attends une minute".encode("utf-8"))
        else:
            self._reply(401, b"pin")
        return False

    def _mp3(self):
        qs = parse_qs(urlparse(self.path).query)
        if not self._auth(qs.get("pin", [""])[0]):
            return
        try:
            import lameenc
        except ImportError:
            return self._reply(500, "lameenc n'est pas installe : relance lancer.bat".encode("utf-8"))
        try:
            q, rate, ch = HUB.subscribe()
        except Exception as ex:
            print("audio :", ex)
            return self._reply(500, str(ex).encode("utf-8"))
        enc = lameenc.Encoder()
        enc.set_bit_rate(128)
        enc.set_in_sample_rate(rate)
        enc.set_channels(2)
        enc.set_quality(5)
        silence = b"\x00" * (ch * 2 * int(rate * 0.1))
        try:
            self.send_response(200)
            self.send_header("Content-Type", "audio/mpeg")
            self.send_header("Accept-Ranges", "none")
            self.send_header("icy-name", "PC Remote")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Connection", "close")
            self.end_headers()
            burst = bytearray()
            for _ in range(3):  # 0,3 s de silence seulement : demarrage rapide sans retard ajoute
                burst += enc.encode(silence if ch == 2 else to_stereo(silence, ch))
            self.wfile.write(bytes(burst))
            self.wfile.flush()
            while True:
                try:
                    data = q.get(timeout=0.1)
                except queue.Empty:
                    data = silence
                if ch != 2:
                    data = to_stereo(data, ch)
                out = enc.encode(data)
                if out:
                    self.wfile.write(bytes(out))
                    self.wfile.flush()
        except Exception:
            pass
        finally:
            HUB.unsubscribe(q)
            self.close_connection = True

    def _screen(self):
        qs = parse_qs(urlparse(self.path).query)
        if not self._auth(qs.get("pin", [""])[0]):
            return
        try:
            import PIL  # noqa: F401
        except ImportError:
            return self._reply(500, "Pillow n'est pas installe : relance lancer.bat".encode("utf-8"))
        lite = qs.get("lite", ["0"])[0] == "1"
        SCREEN.add(lite)
        try:
            self.send_response(200)
            self.send_header("Content-Type", "multipart/x-mixed-replace; boundary=frame")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Connection", "close")
            self.end_headers()
            seq = 0
            while True:
                frame, s2 = SCREEN.wait(seq)
                if frame is None or s2 == seq:
                    continue
                seq = s2
                self.wfile.write(b"--frame\r\nContent-Type: image/jpeg\r\nContent-Length: %d\r\n\r\n" % len(frame))
                self.wfile.write(frame)
                self.wfile.write(b"\r\n")
                self.wfile.flush()
        except Exception:
            pass
        finally:
            SCREEN.remove(lite)
            self.close_connection = True

    def _qr(self):
        if self.client_address[0] not in ("127.0.0.1", "::1", "::ffff:127.0.0.1"):
            return self._reply(403, b"Cette page n'est accessible que depuis le PC.")
        host = socket.gethostname()
        url = "http://%s:%d/?pin=%s" % (local_ip(), PORT, PIN)
        url2 = "http://%s.local:%d/?pin=%s" % (host, PORT, PIN)
        try:
            import qrcode
            import qrcode.image.svg
            img = qrcode.make(url, image_factory=qrcode.image.svg.SvgPathImage, box_size=10, border=2)
            buf = io.BytesIO()
            img.save(buf)
            svg = buf.getvalue().decode("utf-8")
            svg = svg[svg.index("<svg"):]
        except Exception:
            svg = "<p>(QR code indisponible : relance lancer.bat pour installer le module)</p>"
        tsip = tailscale_ip()
        if tsip:
            rurl = "http://%s:%d/?pin=%s" % (tsip, PORT, PIN)
            try:
                img = qrcode.make(rurl, image_factory=qrcode.image.svg.SvgPathImage, box_size=10, border=2)
                b2 = io.BytesIO()
                img.save(b2)
                rsvg = b2.getvalue().decode("utf-8")
                rsvg = rsvg[rsvg.index("<svg"):]
            except Exception:
                rsvg = ""
            remote = '<hr><h2>A distance (4G/5G, autre Wi-Fi)</h2><p>Sur l\'iPhone, ouvre l\'appli <b>Tailscale</b>, connecte-toi avec le meme compte, puis scanne ce code.</p><div class="qr">%s</div><p><a href="%s">%s</a></p>' % (rsvg, rurl, rurl)
        else:
            remote = '<hr><h2>A distance</h2><p>Pas encore active. Double-clique sur <b>acces_distance.bat</b> (voir LISEZMOI), puis relance lancer.bat.</p>'
        page = QR_HTML.replace("@@REMOTE@@", remote).replace("@@SVG@@", svg).replace("@@URL@@", url).replace("@@URL2@@", url2).replace("@@PIN@@", PIN)
        self._reply(200, page.encode("utf-8"), "text/html; charset=utf-8")

    def _audiocheck(self):
        if not self._auth(self.headers.get("X-Pin", "")):
            return
        try:
            import lameenc  # noqa: F401
        except ImportError:
            return self._reply(500, "Module MP3 (lameenc) absent : ferme et relance lancer.bat".encode("utf-8"))
        try:
            q, _, _ = HUB.subscribe()
        except Exception as ex:
            return self._reply(500, str(ex).encode("utf-8"))
        HUB.unsubscribe(q)
        self._reply(200, b"ok")

    def _diag(self):
        if self.client_address[0] not in ("127.0.0.1", "::1", "::ffff:127.0.0.1"):
            return self._reply(403, b"Cette page n'est accessible que depuis le PC.")
        lines = ["DIAGNOSTIC PC REMOTE (version %s)" % VERSION, "Python : " + sys.version.split()[0], ""]
        for mod, role in (("pyaudiowpatch", "capture du son"), ("lameenc", "son ecran eteint (MP3)"),
                          ("PIL", "ecran du PC"), ("qrcode", "QR code")):
            try:
                __import__(mod)
                lines.append("OK       %s (%s)" % (mod, role))
            except Exception as ex:
                lines.append("MANQUANT %s (%s) : %s" % (mod, role, ex))
        lines.append("")
        if IS_WIN:
            try:
                import pyaudiowpatch as pa
                p = pa.PyAudio()
                w = p.get_host_api_info_by_type(pa.paWASAPI)
                d = p.get_device_info_by_index(w["defaultOutputDevice"])
                lines.append("Sortie audio par defaut de Windows : " + d["name"])
                lb = [x["name"] for x in p.get_loopback_device_info_generator()]
                lines.append("Peripheriques de capture du son : " + (", ".join(lb) if lb else "AUCUN"))
                p.terminate()
            except Exception as ex:
                lines.append("AUDIO : ERREUR -> %s" % ex)
        else:
            lines.append("(mode test hors Windows : pas de test audio)")
        self._reply(200, "\n".join(lines).encode("utf-8"))

    def _wsaudio(self):
        qs = parse_qs(urlparse(self.path).query)
        if not self._auth(qs.get("pin", [""])[0]):
            return
        key = self.headers.get("Sec-WebSocket-Key")
        if not key or "websocket" not in self.headers.get("Upgrade", "").lower():
            return self._reply(400, b"websocket")
        try:
            q, rate, ch = HUB.subscribe(30)  # tampon 300 ms : evite les trous (le telephone rattrape l'avance)
        except Exception as ex:
            print("audio :", ex)
            return self._reply(500, str(ex).encode("utf-8"))
        accept = base64.b64encode(hashlib.sha1((key + "258EAFA5-E914-47DA-95CA-C5AB0DC85B11").encode()).digest()).decode()
        try:
            self.wfile.write(("HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n"
                              "Sec-WebSocket-Accept: %s\r\n\r\n" % accept).encode())
            self.wfile.write(ws_frame(0x1, json.dumps({"rate": rate, "ch": ch}).encode()))
            self.wfile.flush()
            while True:
                try:
                    data = q.get(timeout=0.5)
                    self.wfile.write(ws_frame(0x2, data))
                except queue.Empty:
                    self.wfile.write(ws_frame(0x9, b""))  # ping : detecte une deconnexion
                self.wfile.flush()
        except Exception:
            pass
        finally:
            HUB.unsubscribe(q)
            self.close_connection = True

    def _wsin(self):
        """Evenements clavier/souris par WebSocket : une seule connexion, sans attendre de reponse (fluide)."""
        qs = parse_qs(urlparse(self.path).query)
        if not self._auth(qs.get("pin", [""])[0]):
            return
        key = self.headers.get("Sec-WebSocket-Key")
        if not key or "websocket" not in self.headers.get("Upgrade", "").lower():
            return self._reply(400, b"websocket")
        accept = base64.b64encode(hashlib.sha1((key + "258EAFA5-E914-47DA-95CA-C5AB0DC85B11").encode()).digest()).decode()
        rf = self.rfile
        try:
            self.wfile.write(("HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n"
                              "Sec-WebSocket-Accept: %s\r\n\r\n" % accept).encode())
            self.wfile.flush()
            self.connection.settimeout(30)
            while True:
                h = rf.read(2)
                if len(h) < 2:
                    break
                op = h[0] & 15
                ln = h[1] & 127
                if ln == 126:
                    ln = struct.unpack("!H", rf.read(2))[0]
                elif ln == 127:
                    ln = struct.unpack("!Q", rf.read(8))[0]
                if ln > 1 << 20:
                    break
                mask = rf.read(4) if h[1] & 128 else b"\0\0\0\0"
                data = bytearray(rf.read(ln))
                if len(data) < ln:
                    break
                for i in range(len(data)):
                    data[i] ^= mask[i & 3]
                if op == 8:
                    break
                if op == 9:
                    self.wfile.write(ws_frame(0xA, bytes(data)))
                    self.wfile.flush()
                elif op == 1:
                    try:
                        handle(json.loads(bytes(data)))
                    except Exception as ex:
                        print("erreur:", ex)
        except Exception:
            pass
        finally:
            self.close_connection = True

    def _wsmp3(self):
        """MP3 en direct par WebSocket : petits paquets, le telephone controle son retard (ecran eteint)."""
        qs = parse_qs(urlparse(self.path).query)
        if not self._auth(qs.get("pin", [""])[0]):
            return
        key = self.headers.get("Sec-WebSocket-Key")
        if not key or "websocket" not in self.headers.get("Upgrade", "").lower():
            return self._reply(400, b"websocket")
        try:
            import lameenc
        except ImportError:
            return self._reply(500, "Module MP3 (lameenc) absent : ferme et relance lancer.bat".encode("utf-8"))
        try:
            q, rate, ch = HUB.subscribe(12)
        except Exception as ex:
            print("audio :", ex)
            return self._reply(500, str(ex).encode("utf-8"))
        enc = lameenc.Encoder()
        enc.set_bit_rate(128)
        enc.set_in_sample_rate(rate)
        enc.set_channels(2)
        enc.set_quality(7)  # encodage rapide
        silence = b"\x00" * (ch * 2 * int(rate * 0.05))
        accept = base64.b64encode(hashlib.sha1((key + "258EAFA5-E914-47DA-95CA-C5AB0DC85B11").encode()).digest()).decode()
        try:
            self.wfile.write(("HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n"
                              "Sec-WebSocket-Accept: %s\r\n\r\n" % accept).encode())
            self.wfile.write(ws_frame(0x1, json.dumps({"mime": "audio/mpeg"}).encode()))
            self.wfile.flush()
            while True:
                try:
                    data = q.get(timeout=0.05)
                except queue.Empty:
                    data = silence  # rien ne joue sur le PC : on envoie du silence pour garder le flux vivant
                if ch != 2:
                    data = to_stereo(data, ch)
                out = enc.encode(data)
                if out:
                    self.wfile.write(ws_frame(0x2, bytes(out)))
                    self.wfile.flush()
        except Exception:
            pass
        finally:
            HUB.unsubscribe(q)
            self.close_connection = True

    def _audio(self):
        if not self._auth(self.headers.get("X-Pin", "")):
            return
        try:
            q, rate, ch = HUB.subscribe()
        except Exception as ex:
            print("audio :", ex)
            return self._reply(500, str(ex).encode("utf-8"))
        silence = b"\x00" * (ch * 2 * int(rate * 0.1))
        try:
            self.send_response(200)
            self.send_header("Content-Type", "application/octet-stream")
            self.send_header("X-Rate", str(rate))
            self.send_header("X-Channels", str(ch))
            self.send_header("Access-Control-Expose-Headers", "X-Rate, X-Channels")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Connection", "close")
            self.end_headers()
            self.wfile.flush()
            while True:
                try:
                    data = q.get(timeout=0.1)
                except queue.Empty:
                    data = silence
                self.wfile.write(data)
                self.wfile.flush()
        except Exception:
            pass
        finally:
            HUB.unsubscribe(q)
            self.close_connection = True

    def do_GET(self):
        p = urlparse(self.path).path
        if p == "/audio":
            self._audio()
        elif p == "/wsaudio":
            self._wsaudio()
        elif p == "/wsmp3":
            self._wsmp3()
        elif p in ("/apple-touch-icon.png", "/favicon.ico"):
            self._reply(200, ICON, "image/png", cache=True)
        elif p.startswith("/f/") and p.endswith(".woff2") and p[3:-6] in FONTS:
            self._reply(200, FONTS[p[3:-6]], "font/woff2", cache=True)
        elif p == "/stream.mp3":
            self._mp3()
        elif p == "/wsin":
            self._wsin()
        elif p == "/screen":
            self._screen()
        elif p == "/qr":
            self._qr()
        elif p == "/audiocheck":
            self._audiocheck()
        elif p == "/diag":
            self._diag()
        elif p == "/version":
            self._reply(200, json.dumps({"version": VERSION, "build": BUILD}).encode("utf-8"), "application/json")
        elif p in ("/", "/index.html"):
            self._reply(200, HTML.replace("@@VERSION@@", VERSION).replace("@@BUILD@@", str(BUILD)).encode("utf-8"), "text/html; charset=utf-8")
        elif p == "/wakeinfo":
            if not self._auth(self.headers.get("X-Pin", "") or (parse_qs(urlparse(self.path).query).get("pin") or [""])[0]):
                return
            info = {"mac": pc_mac(), "ip": local_ip(), "name": socket.gethostname(), "ts": tailscale_ip()}
            self._reply(200, json.dumps(info).encode("utf-8"), "application/json")
        else:
            self._reply(404)

    def do_POST(self):
        n = int(self.headers.get("Content-Length") or 0)
        raw = self.rfile.read(n)
        if not self._auth(self.headers.get("X-Pin", "")):
            return
        if self.path == "/power":
            try:
                a = json.loads(raw or b"{}").get("action", "")
            except Exception:
                a = ""
            print("alimentation :", a)
            return self._reply(200 if power_action(a) else 400, b"ok")
        if self.path == "/update":
            try:
                req = json.loads(raw or b"{}")
            except Exception:
                req = {}
            return self._reply(200, update_api(req).encode("utf-8"))
        try:
            handle(json.loads(raw))
        except Exception as ex:
            print("erreur:", ex)
            return self._reply(400)
        self._reply(200, b"ok")


def tailscale_ip():
    """Adresse Tailscale (100.64.0.0/10) de ce PC, ou None si Tailscale n'est pas actif."""
    import re, subprocess
    pat = re.compile(r"\b100\.(?:6[4-9]|[7-9]\d|1[01]\d|12[0-7])\.\d{1,3}\.\d{1,3}\b")
    try:
        out = subprocess.run(["tailscale", "ip", "-4"], capture_output=True, timeout=5).stdout.decode("utf-8", "replace")
        m = pat.search(out)
        if m:
            return m.group(0)
    except Exception:
        pass
    try:
        out = subprocess.run(["ipconfig"] if os.name == "nt" else ["ip", "-4", "addr"], capture_output=True, timeout=10).stdout.decode("cp850", "replace")
        m = pat.search(out)
        if m:
            return m.group(0)
    except Exception:
        pass
    return None


def pc_mac():
    """Adresse MAC de la carte reseau utilisee (pour Wake-on-LAN)."""
    import re, subprocess
    ip = local_ip()
    try:
        out = subprocess.run(["ipconfig", "/all"], capture_output=True, timeout=10).stdout.decode("cp850", "replace")
        for bloc in re.split(r"\r?\n\r?\n(?=\S)", out):
            if ip in bloc:
                m = re.search(r"([0-9A-Fa-f]{2}(?:-[0-9A-Fa-f]{2}){5})", bloc)
                if m:
                    return m.group(1).upper().replace("-", ":")
    except Exception:
        pass
    n = uuid.getnode()
    return ":".join("%02X" % ((n >> (8 * i)) & 255) for i in range(5, -1, -1))


POWER_CMDS = {
    "shutdown": ["shutdown", "/s", "/t", "15"],
    "restart": ["shutdown", "/r", "/t", "15"],
    "cancel": ["shutdown", "/a"],
    "sleep": ["rundll32.exe", "powrprof.dll,SetSuspendState", "0,1,0"],
    "lock": ["rundll32.exe", "user32.dll,LockWorkStation"],
}


def power_action(name):
    cmd = POWER_CMDS.get(name)
    if not cmd:
        return False
    if os.name != "nt":
        print("[test] alimentation :", " ".join(cmd))
        return True
    import subprocess
    if name == "sleep":
        # laisse le temps a la reponse HTTP de partir avant la mise en veille
        threading.Timer(1.5, lambda: subprocess.Popen(cmd)).start()
    else:
        subprocess.Popen(cmd, creationflags=0x08000000)
    return True


def local_ip():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("10.255.255.255", 1))
        return s.getsockname()[0]
    except Exception:
        return "127.0.0.1"
    finally:
        s.close()


QR_HTML = r"""<!doctype html>
<html lang="fr"><head><meta charset="utf-8"><title>PC Remote : connecter l'iPhone</title><link rel="icon" href="/apple-touch-icon.png" type="image/png">
<style>
@font-face{font-family:"Press Start 2P";src:url(/f/ps2p.woff2) format("woff2")}
body{margin:0;background:radial-gradient(#000 .7px,transparent 1.1px) 0 0/8px 8px,#fff;color:#000;font-family:"Press Start 2P","Courier New",monospace;font-size:11px;line-height:1.9;display:flex;justify-content:center}
main{max-width:640px;margin:26px 16px;padding:28px;text-align:center;background:#fff;box-shadow:0 -4px #000,0 4px #000,-4px 0 #000,4px 0 #000}
h1{font-size:18px;font-weight:400;margin:10px 0 16px}h2{font-size:13px;font-weight:400}hr{border:0;border-top:4px solid #000;margin:22px 0}
.mascot{width:84px;height:84px;animation:bob 1.2s steps(2) infinite}.mascot .i{fill:#000}.mascot .p{fill:#fff}
@keyframes bob{50%{transform:translateY(-3px)}}
.qr{display:inline-block;padding:14px;background:#fff;box-shadow:0 -4px #000,0 4px #000,-4px 0 #000,4px 0 #000;margin:10px 0}
.qr svg{width:300px;height:300px;display:block}
a{color:#000;word-break:break-all}
li{text-align:left;margin:8px 0}
code{background:#000;color:#fff;padding:4px 10px;font-size:16px}
</style></head><body><main>
<svg class="mascot" viewBox="0 0 16 16" shape-rendering="crispEdges" aria-hidden="true"><path class="p" d="M1 5h14v1h-14zM1 6h14v1h-14zM1 7h3v1h-3zM6 7h5v1h-5zM13 7h2v1h-2zM1 8h2v1h-2zM6 8h4v1h-4zM13 8h2v1h-2zM1 9h2v1h-2zM6 9h4v1h-4zM13 9h2v1h-2zM1 10h14v1h-14zM1 11h3v1h-3zM5 11h6v1h-6zM12 11h3v1h-3zM1 12h4v1h-4zM11 12h4v1h-4zM1 13h14v1h-14z"/><path class="i" d="M3 0h1v1h-1zM12 0h1v1h-1zM4 1h1v1h-1zM11 1h1v1h-1zM5 2h1v1h-1zM10 2h1v1h-1zM6 3h1v1h-1zM9 3h1v1h-1zM1 4h14v1h-14zM0 5h1v1h-1zM15 5h1v1h-1zM0 6h1v1h-1zM15 6h1v1h-1zM0 7h1v1h-1zM15 7h1v1h-1zM0 8h1v1h-1zM15 8h1v1h-1zM0 9h1v1h-1zM15 9h1v1h-1zM0 10h1v1h-1zM15 10h1v1h-1zM0 11h1v1h-1zM4 11h1v1h-1zM11 11h1v1h-1zM15 11h1v1h-1zM0 12h1v1h-1zM5 12h6v1h-6zM15 12h1v1h-1zM0 13h1v1h-1zM15 13h1v1h-1zM1 14h14v1h-14zM2 15h2v1h-2zM12 15h2v1h-2z"/><path class="i eyes" d="M4 7h2v1h-2zM11 7h2v1h-2zM3 8h3v1h-3zM10 8h3v1h-3zM3 9h3v1h-3zM10 9h3v1h-3z"/></svg><h1>Connecter l'iPhone</h1>
<p>Ouvre l'appareil photo de l'iPhone et scanne ce code, puis touche le lien qui apparait. Aucun PIN a saisir.</p>
<div class="qr">@@SVG@@</div>
<p>Lien direct : <a href="@@URL@@">@@URL@@</a><br>PIN : <code>@@PIN@@</code></p>
<ol>
<li>Pour un acces en un toucher : dans Safari, touche <b>Partager</b> puis <b>Sur l'ecran d'accueil</b>.</li>
<li>L'iPhone et le PC doivent etre sur le meme Wi-Fi.</li>
<li>Si l'adresse change un jour, relance lancer.bat et rescanne ce code.</li>
</ol>
@@REMOTE@@
</main></body></html>
"""


HTML = r"""<!doctype html>
<html lang="fr" data-theme="mixte"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,maximum-scale=1,user-scalable=no,viewport-fit=cover">
<meta name="apple-mobile-web-app-capable" content="yes"><meta name="mobile-web-app-capable" content="yes"><meta name="apple-mobile-web-app-status-bar-style" content="black-translucent"><meta name="apple-mobile-web-app-title" content="PC Remote">
<meta name="theme-color" content="#ffffff">
<link rel="icon" href="/apple-touch-icon.png" type="image/png">
<link rel="apple-touch-icon" href="/apple-touch-icon.png">
<title>PC Remote</title>
<style>
@font-face{font-family:"Press Start 2P";src:url(/f/ps2p.woff2) format("woff2");font-display:swap}
@font-face{font-family:"VT323";src:url(/f/vt323.woff2) format("woff2");font-display:swap}
@font-face{font-family:"Bangers";src:url(/f/bangers.woff2) format("woff2");font-display:swap}
:root{--ink:#000;--paper:#fff;
--fb:"Press Start 2P","Courier New",ui-monospace,monospace;--fi:"VT323","Courier New",ui-monospace,monospace;--fh:"Press Start 2P","Courier New",monospace;
--fs:8px;--r:0;--pad:5px 5px 6px 5px;
--outline:0 -3px 0 0 var(--ink),0 3px 0 0 var(--ink),-3px 0 0 0 var(--ink),3px 0 0 0 var(--ink);
--frame:var(--outline);--frame-press:var(--outline);
--bevel:inset -4px -4px 0 0 var(--ink);--bevel-press:inset 4px 4px 0 0 var(--ink);--bevel-on:inset -4px -4px 0 0 var(--paper);
--dots:radial-gradient(var(--ink) .7px,transparent 1.1px) 0 0/8px 8px,var(--paper);
--dots-big:radial-gradient(var(--ink) 1.3px,transparent 1.8px) 0 0/10px 10px,var(--paper)}
html[data-theme="pixel"]{--ink:#fff;--paper:#000}
html[data-theme="cartoon"]{--fb:"Bangers","Comic Sans MS","Marker Felt",system-ui,sans-serif;--fi:var(--fb);--fh:var(--fb);--fs:17px;--r:16px;--pad:6px 12px 13px 6px;
--frame:0 0 0 4px var(--ink),5px 6px 0 4px var(--ink);--frame-press:0 0 0 4px var(--ink),1px 2px 0 4px var(--ink);
--bevel:inset 0 0 0 0 transparent;--bevel-press:inset 0 0 0 0 transparent;--bevel-on:inset 0 0 0 0 transparent}
*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}
html,body{margin:0;height:100%;background:var(--paper);color:var(--ink);font-family:var(--fb);font-size:var(--fs);line-height:1.5;overflow:hidden;-webkit-font-smoothing:none}
body{background:var(--dots)}
html[data-theme="pixel"] body{background:var(--paper)}
html[data-theme="pixel"] body::after{content:"";position:fixed;inset:0;pointer-events:none;z-index:50;background:repeating-linear-gradient(0deg,transparent 0 2px,rgba(255,255,255,.06) 2px 3px)}
#app>*{flex:none}
#app{display:flex;flex-direction:column;height:100%;padding:calc(env(safe-area-inset-top) + 8px) 8px calc(env(safe-area-inset-bottom) + 14px);gap:4px;overflow-y:auto}
#top{display:flex;align-items:center;gap:6px;padding:4px 4px 0}
.hd{flex:1;min-width:0}
.mascot{width:54px;height:54px;flex:none;animation:bob 1.2s steps(2) infinite}
.mascot .i{fill:var(--ink)}.mascot .p{fill:var(--paper)}
.mascot .eyes{transform-box:fill-box;transform-origin:center;animation:blink 4.5s steps(1) infinite}
@keyframes bob{50%{transform:translateY(-3px)}}
@keyframes blink{0%,93%,100%{transform:scaleY(1)}95%,98%{transform:scaleY(.15)}}
@keyframes blinkc{50%{opacity:0}}
.title{font-family:var(--fh);font-size:13px;letter-spacing:1px;margin:0 0 8px 16px;display:inline-block;background:var(--paper);padding:2px 6px}
html[data-theme="cartoon"] .title{font-size:36px;line-height:1;letter-spacing:2px;color:var(--paper);-webkit-text-stroke:3px var(--ink);paint-order:stroke fill;text-shadow:3px 3px 0 var(--ink);background:none;padding:0;margin-bottom:12px}
#st{position:relative;margin:2px 6px 6px 18px;padding:10px 12px;font-size:9px;line-height:1.5;background:var(--paper);color:var(--ink);box-shadow:var(--frame);border-radius:var(--r)}
html[data-theme="cartoon"] #st{display:flex;align-items:center;min-height:52px;font-size:20px;line-height:1;padding:0 18px}
html[data-theme="cartoon"] .tools small{font-size:15px}
#st::before{content:"";position:absolute;left:-15px;top:50%;margin-top:-7px;border:7px solid transparent;border-left:0;border-right:11px solid var(--ink)}
#st.ok{background:var(--ink);color:var(--paper)}
#st.ko::after{content:" _";animation:blinkc 1s steps(1) infinite}
.tools{display:flex;gap:10px;align-items:center;padding:6px 6px 8px}
.tools button{flex:0 1 auto;padding:9px 10px}
.tools small{margin-left:auto;font-size:8px;background:var(--paper);padding:3px 5px}
button{font:inherit;font-size:var(--fs);line-height:1.3;color:var(--ink);background:var(--paper);border:0;border-radius:var(--r);padding:12px 6px;flex:1;min-width:0;cursor:pointer;box-shadow:var(--frame),var(--bevel)}
html[data-theme="cartoon"] button{letter-spacing:1px;padding:8px 6px}
button:active{transform:translate(2px,2px);box-shadow:var(--frame-press),var(--bevel-press)}
button.on{background:var(--ink);color:var(--paper);box-shadow:var(--frame),var(--bevel-on)}
.row{display:flex;gap:11px;padding:var(--pad)}
.row.scroll{overflow-x:auto;scrollbar-width:none}.row.scroll::-webkit-scrollbar{display:none}
.row.scroll button{flex:0 0 auto;min-width:50px;padding:12px 10px}
html[data-theme="cartoon"] .row.scroll button{padding:8px 12px}
#pad{flex:1 0 170px;margin:6px 6px 8px;background:var(--dots-big);box-shadow:var(--frame);border-radius:var(--r);touch-action:none;user-select:none;-webkit-user-select:none;display:flex;align-items:center;justify-content:center;text-align:center}
#pad span{background:var(--paper);padding:9px 12px;font-size:10px;box-shadow:var(--outline);border-radius:var(--r)}
html[data-theme="cartoon"] #pad span{font-size:22px;box-shadow:0 0 0 3px var(--ink);padding:4px 16px}
#audmsg{margin:4px 6px 6px;padding:7px 9px;font-size:8px;line-height:1.7;background:var(--paper);box-shadow:var(--frame);border-radius:var(--r)}
#audmsg:empty{display:none}
#audmsg.err{background:var(--ink);color:var(--paper);font-size:9px}
html[data-theme="cartoon"] #audmsg{font-size:15px}
.cap{margin:6px 8px 0;align-self:flex-start;padding:5px 8px;font-size:8px;background:var(--paper);box-shadow:var(--outline)}
html[data-theme="cartoon"] .cap{font-size:15px;box-shadow:0 0 0 3px var(--ink);border-radius:10px}
#in,#updurl,#lpin{display:block;width:calc(100% - 12px);margin:8px 6px;padding:9px 12px;font-family:var(--fi);font-size:21px;line-height:1.2;color:var(--ink);background:var(--paper);border:0;border-radius:var(--r);box-shadow:var(--frame);outline:none}
#in::placeholder,#updurl::placeholder,#lpin::placeholder{color:var(--ink);opacity:.55}
label{display:block;margin:8px 6px;padding:8px 10px;font-size:8px;background:var(--paper);box-shadow:var(--frame);border-radius:var(--r)}
html[data-theme="cartoon"] label{font-size:16px;text-transform:none}
#sens{-webkit-appearance:none;appearance:none;display:block;width:100%;height:26px;margin:4px 0 0;background:transparent}
#sens::-webkit-slider-runnable-track{height:6px;background:var(--ink)}
#sens::-webkit-slider-thumb{-webkit-appearance:none;width:20px;height:20px;margin-top:-7px;background:var(--paper);border:4px solid var(--ink);border-radius:var(--r)}
#sens::-moz-range-track{height:6px;background:var(--ink)}
#sens::-moz-range-thumb{width:12px;height:12px;background:var(--paper);border:4px solid var(--ink);border-radius:0}
details{margin:8px 6px;padding:8px 10px;background:var(--paper);box-shadow:var(--frame);border-radius:var(--r)}
summary{cursor:pointer;list-style:none;font-size:8px}
html[data-theme="cartoon"] summary{font-size:16px;text-transform:none}
summary::-webkit-details-marker{display:none}
summary::before{content:"> "}details[open] summary::before{content:"v "}
details .row{padding:8px 4px 10px}
#updurl{margin:0;flex:1;min-width:0;width:auto}
#updset{flex:none;padding:9px 14px}
#updmsg{font-size:8px;line-height:1.7;word-break:break-word}
html[data-theme="cartoon"] #updmsg{font-size:15px}
#login{position:fixed;inset:0;background:var(--dots);z-index:20;display:none;align-items:center;justify-content:center;padding:26px}
.lcard{width:100%;max-width:340px;text-align:center;background:var(--paper);padding:20px 14px 18px;box-shadow:var(--frame);border-radius:var(--r)}
.lcard .mascot{width:92px;height:92px;display:block;margin:0 auto 8px}
.lcard h2{font-family:var(--fh);font-size:14px;margin:6px 0 12px;font-weight:400}
html[data-theme="cartoon"] .lcard h2{font-size:34px;color:var(--paper);-webkit-text-stroke:3px var(--ink);paint-order:stroke fill;text-shadow:3px 3px 0 var(--ink)}
.lcard p{font-size:8px;line-height:1.9;margin:0 0 6px}
html[data-theme="cartoon"] .lcard p{font-size:16px}
#lpin{font-size:34px;text-align:center;letter-spacing:6px;margin:12px 6px 6px}
#lmsg{min-height:22px;font-size:8px;line-height:1.7;margin:8px 0 12px}
html[data-theme="cartoon"] #lmsg{font-size:15px}
#lgo{width:calc(100% - 12px);flex:none;margin:6px;padding:14px 6px}
#scr{position:fixed;inset:0;background:#000;z-index:10;display:none}
#scrImg{width:100%;height:100%;object-fit:contain;touch-action:none;user-select:none;-webkit-user-select:none;-webkit-touch-callout:none}
#scrBar{position:fixed;top:env(safe-area-inset-top);left:0;right:0;display:flex;gap:10px;padding:10px 12px 14px;background:var(--paper);border-bottom:4px solid var(--ink)}
#scrBar button{padding:9px 4px}
#sIn{position:fixed;bottom:0;left:0;width:2px;height:2px;opacity:.02;font-size:16px;border:0;padding:0}
/* barre de l'ecran du PC : compacte, tout sur une ligne, pour laisser la place a l'image */
html[data-theme="cartoon"] #scrBar{gap:6px;padding:6px 8px 10px;border-bottom-width:3px}
html[data-theme="cartoon"] #scrBar button{font-size:14px;padding:3px 2px 8px;white-space:nowrap;min-height:0;letter-spacing:0}
html[data-theme="pixel"] #scrBar,html[data-theme="mixte"] #scrBar{gap:6px;padding:6px 8px 10px}
html[data-theme="pixel"] #scrBar button,html[data-theme="mixte"] #scrBar button{font-size:7px;padding:8px 2px;white-space:nowrap}
/* paysage : en-tete reduit pour garder la place au pave tactile */
@media (orientation:landscape) and (max-height:520px){
#top .mascot{width:34px;height:34px}
.title{margin-bottom:2px}
html[data-theme="cartoon"] .title{font-size:22px;margin-bottom:4px;-webkit-text-stroke:2px var(--ink);text-shadow:2px 2px 0 var(--ink)}
html[data-theme="pixel"] .title,html[data-theme="mixte"] .title{font-size:9px}
#st{margin-bottom:2px}
html[data-theme="cartoon"] #st{min-height:34px;font-size:16px}
html[data-theme="pixel"] #st,html[data-theme="mixte"] #st{padding:6px 10px}
}
button{min-height:44px}
.tools button{min-height:40px}
#scrBar button{min-height:40px}
#conf{position:fixed;inset:0;z-index:40;background:rgba(0,0,0,.6);display:none;align-items:center;justify-content:center;padding:20px}
#conf.on{display:flex}
#conf .cbox{background:var(--paper,#fff);color:var(--ink,#000);border:4px solid var(--ink,#000);padding:18px;max-width:340px;width:100%}
#conf p{margin:0 0 14px;line-height:1.6;white-space:pre-line}
#pmsg{margin-top:8px;line-height:1.6;white-space:pre-line;word-break:break-word}
#scr{height:100vh;height:100dvh}
#sTab{position:fixed;top:calc(env(safe-area-inset-top) + 8px);right:8px;z-index:12;width:44px;height:44px;min-height:44px;padding:0;font-size:22px;line-height:1;opacity:.35;display:none}
#scr.full #scrBar{display:none}
#scr.full #sTab{display:block}
#sKT{position:fixed;top:calc(env(safe-area-inset-top) + 58px);right:8px;z-index:12;width:44px;height:44px;min-height:44px;padding:0;font-size:22px;line-height:1;opacity:.35;display:none}
#scr.full #sKT{display:block}
#sTab,#sKT,#scrBar button{touch-action:manipulation}
#scr{overscroll-behavior:none;touch-action:none}
html,body{overscroll-behavior:none}
html[data-theme="cartoon"] #scrBar button{min-height:0}
</style></head><body><div id="app">
<div id="top"><svg class="mascot" viewBox="0 0 16 16" shape-rendering="crispEdges" aria-hidden="true"><path class="p" d="M1 5h14v1h-14zM1 6h14v1h-14zM1 7h3v1h-3zM6 7h5v1h-5zM13 7h2v1h-2zM1 8h2v1h-2zM6 8h4v1h-4zM13 8h2v1h-2zM1 9h2v1h-2zM6 9h4v1h-4zM13 9h2v1h-2zM1 10h14v1h-14zM1 11h3v1h-3zM5 11h6v1h-6zM12 11h3v1h-3zM1 12h4v1h-4zM11 12h4v1h-4zM1 13h14v1h-14z"/><path class="i" d="M3 0h1v1h-1zM12 0h1v1h-1zM4 1h1v1h-1zM11 1h1v1h-1zM5 2h1v1h-1zM10 2h1v1h-1zM6 3h1v1h-1zM9 3h1v1h-1zM1 4h14v1h-14zM0 5h1v1h-1zM15 5h1v1h-1zM0 6h1v1h-1zM15 6h1v1h-1zM0 7h1v1h-1zM15 7h1v1h-1zM0 8h1v1h-1zM15 8h1v1h-1zM0 9h1v1h-1zM15 9h1v1h-1zM0 10h1v1h-1zM15 10h1v1h-1zM0 11h1v1h-1zM4 11h1v1h-1zM11 11h1v1h-1zM15 11h1v1h-1zM0 12h1v1h-1zM5 12h6v1h-6zM15 12h1v1h-1zM0 13h1v1h-1zM15 13h1v1h-1zM1 14h14v1h-14zM2 15h2v1h-2zM12 15h2v1h-2z"/><path class="i eyes" d="M4 7h2v1h-2zM11 7h2v1h-2zM3 8h3v1h-3zM10 8h3v1h-3zM3 9h3v1h-3zM10 9h3v1h-3z"/></svg><div class="hd"><div class="title">PC REMOTE</div><div id="st" class="ko">Connexion...</div></div></div>
<div class="tools"><button id="theme">Style</button><button id="out">Déconnexion</button><small>@@VERSION@@</small></div>
<div id="pad"><span>Pavé tactile</span></div>
<div class="row"><button data-c="l">Clic gauche</button><button data-c="m">Milieu</button><button data-c="r">Clic droit</button></div>
<div class="row"><button id="aud">Son temps réel</button><button id="bg">Son écran éteint</button></div>
<div id="audmsg"></div>
<div class="row"><button id="scrBtn">Téléphone = écran du PC</button></div>
<div class="row" id="mods"></div>
<div class="row scroll" id="keys"></div>
<div class="row scroll" id="short"></div>
<div class="row scroll" id="fk"></div>
<div class="cap">Clavier du PC : touche ici et tape</div>
<input id="in" autocapitalize="off" autocorrect="off" autocomplete="off" spellcheck="false" enterkeyhint="send" placeholder="Touche ici pour taper sur le PC">
<label>Sensibilité <input id="sens" type="range" min="0.5" max="4" step="0.1" value="1.8"></label>
<details id="rem"><summary>Accès à distance</summary>
<label><input type="checkbox" id="lite"> Économie de données (écran PC léger)</label>
<div id="rmsg">...</div></details>
<details id="pwr"><summary>Alimentation du PC</summary>
<div class="row"><button id="pOff">Éteindre</button><button id="pRst">Redémarrer</button></div>
<div class="row"><button id="pSlp">Veille</button><button id="pLck">Verrouiller</button></div>
<div class="row"><button id="pCan">Annuler l'extinction</button></div>
<div class="row"><button id="pOn">Allumer le PC</button></div><div id="pmsg"></div></details>
<div id="conf"><div class="cbox"><p id="ctxt"></p><div class="row"><button id="cNo">Non</button><button id="cYes">Oui</button></div></div></div>
<details><summary>Mises à jour (@@VERSION@@)</summary>
<div class="row"><input id="updurl" inputmode="url" autocapitalize="off" autocorrect="off" placeholder="Adresse des mises à jour (https://...)"><button id="updset">OK</button></div>
<div class="row"><button id="updgo">Vérifier maintenant</button></div><div id="updmsg"></div></details>
</div>
<div id="login"><div class="lcard"><svg class="mascot" viewBox="0 0 16 16" shape-rendering="crispEdges" aria-hidden="true"><path class="p" d="M1 5h14v1h-14zM1 6h14v1h-14zM1 7h3v1h-3zM6 7h5v1h-5zM13 7h2v1h-2zM1 8h2v1h-2zM6 8h4v1h-4zM13 8h2v1h-2zM1 9h2v1h-2zM6 9h4v1h-4zM13 9h2v1h-2zM1 10h14v1h-14zM1 11h3v1h-3zM5 11h6v1h-6zM12 11h3v1h-3zM1 12h4v1h-4zM11 12h4v1h-4zM1 13h14v1h-14z"/><path class="i" d="M3 0h1v1h-1zM12 0h1v1h-1zM4 1h1v1h-1zM11 1h1v1h-1zM5 2h1v1h-1zM10 2h1v1h-1zM6 3h1v1h-1zM9 3h1v1h-1zM1 4h14v1h-14zM0 5h1v1h-1zM15 5h1v1h-1zM0 6h1v1h-1zM15 6h1v1h-1zM0 7h1v1h-1zM15 7h1v1h-1zM0 8h1v1h-1zM15 8h1v1h-1zM0 9h1v1h-1zM15 9h1v1h-1zM0 10h1v1h-1zM15 10h1v1h-1zM0 11h1v1h-1zM4 11h1v1h-1zM11 11h1v1h-1zM15 11h1v1h-1zM0 12h1v1h-1zM5 12h6v1h-6zM15 12h1v1h-1zM0 13h1v1h-1zM15 13h1v1h-1zM1 14h14v1h-14zM2 15h2v1h-2zM12 15h2v1h-2z"/><path class="i eyes" d="M4 7h2v1h-2zM11 7h2v1h-2zM3 8h3v1h-3zM10 8h3v1h-3zM3 9h3v1h-3zM10 9h3v1h-3z"/></svg><h2>Connexion au PC</h2><p>Saisis le code PIN affiché sur le PC, ou scanne le QR code.</p><input id="lpin" inputmode="numeric" pattern="[0-9]*" maxlength="6" autocomplete="off" placeholder="000000"><div id="lmsg"></div><button id="lgo">Se connecter</button></div></div>
<div id="scr">
<img id="scrImg" alt="">
<div id="scrBar"><button id="sBack">Retour</button><button id="sKb">Clavier</button><button id="sDrag">Glisser</button><button id="sRight">Droit</button><button id="sMore">Plein</button></div>
<button id="sTab" aria-label="Menu">&#9776;</button><button id="sKT" aria-label="Clavier">&#9000;</button>
<input id="sIn" autocapitalize="off" autocorrect="off" autocomplete="off" spellcheck="false">
</div>
<script>
let PIN=""; try{PIN=localStorage.getItem("pin")||""}catch(e){}
const qp=new URLSearchParams(location.search).get("pin");if(qp){PIN=qp;try{localStorage.setItem("pin",qp)}catch(e){}}
let SENS=1.8; try{SENS=parseFloat(localStorage.getItem("sens"))||1.8}catch(e){}
const sens=document.getElementById("sens"); sens.value=SENS;
sens.oninput=()=>{SENS=parseFloat(sens.value); try{localStorage.setItem("sens",SENS)}catch(e){}};
const st=document.getElementById("st");
// Style de l'interface : mixte (pixel + cartoon 60s), pixel (nuit) ou cartoon, tout en noir et blanc
const THEMES=["mixte","pixel","cartoon"],TNAME={mixte:"Mixte",pixel:"Pixel",cartoon:"Cartoon"};
let theme="mixte";try{theme=localStorage.getItem("theme")||"mixte"}catch(e){}
function applyTheme(){if(!THEMES.includes(theme))theme="mixte";document.documentElement.setAttribute("data-theme",theme);document.getElementById("theme").textContent="Style : "+TNAME[theme]}
document.getElementById("theme").onclick=()=>{theme=THEMES[(THEMES.indexOf(theme)+1)%THEMES.length];try{localStorage.setItem("theme",theme)}catch(e){}applyTheme()};
applyTheme();

function setStatus(ok){st.textContent=ok?"Connecté au PC":"Hors ligne";st.className=ok?"ok":"ko"}
let q=[],sending=false,ws=null,wsOk=false,wsTry=0;
function ev(e){const l=q[q.length-1]; if(e.t==="m"&&l&&l.t==="m"){l.x+=e.x;l.y+=e.y}else if(e.t==="a"&&l&&l.t==="a"){l.x=e.x;l.y=e.y}else q.push(e)}
function openWS(){if(!authed||ws)return;let w;try{w=new WebSocket((location.protocol==="https:"?"wss://":"ws://")+location.host+"/wsin?pin="+encodeURIComponent(PIN))}catch(e){return}
  ws=w;w.onopen=()=>{wsOk=true;wsTry=0;setStatus(true)};
  w.onclose=w.onerror=()=>{if(ws!==w)return;ws=null;wsOk=false;wsTry++;if(authed)setTimeout(openWS,Math.min(5000,500*wsTry))}}
async function flush(){
  if(!authed){q=[];return} if(!q.length)return;
  if(!ws&&!wsOk)openWS();
  if(wsOk&&ws&&ws.readyState===1){if(ws.bufferedAmount>65536)return;const b=q;q=[];try{ws.send(JSON.stringify(b));return}catch(e){q=b.concat(q)}}
  if(sending)return; sending=true; const b=q; q=[];
  try{const r=await fetch("/e",{method:"POST",headers:{"X-Pin":PIN,"Content-Type":"application/json"},body:JSON.stringify(b)});
    if(r.status===401){authFail()}else setStatus(r.ok)}
  catch(e){setStatus(false)}
  sending=false}
setInterval(flush,8);
setInterval(()=>{if(authed)ev({t:"ping"})},4000);
const VERSION="@@VERSION@@",BUILD=@@BUILD@@;
let authed=false;
const login=document.getElementById("login"),lpin=document.getElementById("lpin"),lmsg=document.getElementById("lmsg");
async function checkPin(p){
  try{const r=await fetch("/e",{method:"POST",headers:{"X-Pin":p,"Content-Type":"application/json"},body:'[{"t":"ping"}]'});
    return r.status===200?"ok":(r.status===401?"bad":(r.status===429?"lock":"err"))}catch(e){return "err"}}
function showLogin(msg){authed=false;try{if(ws){const w=ws;ws=null;wsOk=false;w.close()}}catch(e){}setStatus(false);st.textContent="Non connecté";login.style.display="flex";lmsg.textContent=msg||"";lpin.value=""}
function authFail(){if(login.style.display==="flex")return;PIN="";try{localStorage.removeItem("pin")}catch(e){}showLogin("Code incorrect ou expiré. Saisis le code affiché sur le PC.")}
function askPin(){authFail()}
async function tryLogin(p){
  const r=await checkPin(p);
  if(r==="ok"){PIN=p;authed=true;try{localStorage.setItem("pin",p)}catch(e){}login.style.display="none";setStatus(true);openWS();return true}
  showLogin(r==="bad"?"Code incorrect.":(r==="lock"?"Trop d'essais : attends une minute.":"PC injoignable : vérifie le Wi-Fi et que lancer.bat est ouvert."));return false}
async function startAuth(){if(PIN){await tryLogin(PIN)}else showLogin("Saisis le code PIN affiché sur le PC.")}
document.getElementById("lgo").onclick=()=>tryLogin(lpin.value.trim());
lpin.addEventListener("keydown",e=>{if(e.key==="Enter")tryLogin(lpin.value.trim())});
function logout(){stopAudio();stopBg();closeScreen();PIN="";try{localStorage.removeItem("pin")}catch(e){}try{history.replaceState(null,"",location.pathname)}catch(e){}showLogin("Déconnecté.")}
document.getElementById("out").onclick=logout;
startAuth();

// Modificateurs (à usage unique)
const active=new Set(), modBtns={};
[["Ctrl","ctrl"],["Alt","alt"],["Maj","shift"],["Win","win"]].forEach(([l,m])=>{
  const b=document.createElement("button");b.textContent=l;
  b.onclick=()=>{active.has(m)?active.delete(m):active.add(m);b.classList.toggle("on",active.has(m))};
  modBtns[m]=b;document.getElementById("mods").appendChild(b)});
function takeMods(){const a=[...active];active.clear();Object.values(modBtns).forEach(b=>b.classList.remove("on"));return a}
function key(vk,mods){ev({t:"k",vk:vk,mods:mods||takeMods()})}
function mk(id,list,fn){list.forEach(x=>{const b=document.createElement("button");b.textContent=x[0];b.onclick=()=>fn(x);document.getElementById(id).appendChild(b)})}
mk("keys",[["Esc",27],["Tab",9],["Suppr",46],["Effacer",8],["Entrée",13],["Gauche",37],["Haut",38],["Bas",40],["Droite",39],["Début",36],["Fin",35],["Page +",33],["Page -",34]],x=>key(x[1]));
mk("short",[["Copier",["ctrl"],67],["Coller",["ctrl"],86],["Couper",["ctrl"],88],["Tout",["ctrl"],65],["Annuler",["ctrl"],90],["Alt+Tab",["alt"],9],["Win+D",["win"],68],["Verrouiller",["win"],76],["Vol -",[],174],["Vol +",[],175],["Muet",[],173],["Lecture",[],179]],x=>key(x[2],x[1]));
mk("fk",Array.from({length:12},(_,i)=>["F"+(i+1),112+i]),x=>key(x[1]));
document.querySelectorAll("[data-c]").forEach(b=>b.onclick=()=>ev({t:"c",b:b.dataset.c}));

// Son du PC -> iPhone en temps réel (WebAudio + lecture silencieuse : continue écran éteint)
const aud=document.getElementById("aud");let actx=null,nextT=0,abortC=null,silent=null,audWanted=false,audTimer=null,wsRef=null,useFetch=false,lead=0.1;
function audSay(t){amsg.textContent=t||"";amsg.className=""}
function silentWav(){const n=8000,b=new ArrayBuffer(44+n),v=new DataView(b);const w=(o,s)=>{for(let i=0;i<s.length;i++)v.setUint8(o+i,s.charCodeAt(i))};
  w(0,"RIFF");v.setUint32(4,36+n,true);w(8,"WAVEfmt ");v.setUint32(16,16,true);v.setUint16(20,1,true);v.setUint16(22,1,true);v.setUint32(24,8000,true);v.setUint32(28,8000,true);v.setUint16(32,1,true);v.setUint16(34,8,true);w(36,"data");v.setUint32(40,n,true);
  new Uint8Array(b,44).fill(128);return URL.createObjectURL(new Blob([b],{type:"audio/wav"}))}
function stopAudio(msg){audWanted=false;clearTimeout(audTimer);try{wsRef&&wsRef.close()}catch(e){}wsRef=null;try{abortC&&abortC.abort()}catch(e){}try{actx&&actx.close()}catch(e){}try{silent&&silent.pause()}catch(e){}
  actx=null;abortC=null;silent=null;aud.classList.remove("on");aud.textContent=msg||"Son temps réel";
  try{if("mediaSession" in navigator)navigator.mediaSession.playbackState="none"}catch(e){}}
function audFail(t){stopAudio();audSay(t+" (diagnostic : ouvre http://localhost:"+location.port+"/diag sur le PC)");amsg.className="err";
  aud.textContent="Son indisponible : voir ci-dessous";setTimeout(()=>{if(!audWanted)aud.textContent="Son temps réel"},6000)}
let rs=null;
function playChunk(u8,rate,ch){const oc=Math.min(ch,2),n=Math.floor(u8.length/(ch*2)),dv=new DataView(u8.buffer,u8.byteOffset,u8.length);if(!n)return;
  const sr=actx.sampleRate;let ab;
  if(Math.abs(sr-rate)<1){ab=actx.createBuffer(oc,n,sr);
    for(let c=0;c<oc;c++){const d=ab.getChannelData(c);for(let i=0;i<n;i++)d[i]=dv.getInt16((i*ch+c)*2,true)/32768}}
  else{ /* rééchantillonnage continu d'un paquet à l'autre : évite les claquements aux jonctions */
    if(!rs||rs.rate!==rate||rs.sr!==sr){rs={rate,sr,pos:0,last:new Float32Array(oc)}}
    const ratio=rate/sr,m=Math.max(0,Math.ceil((n-1-rs.pos)/ratio)),outs=[];
    ab=actx.createBuffer(oc,Math.max(1,m),sr);
    for(let c=0;c<oc;c++){const d=ab.getChannelData(c);let idx=rs.pos,k=0;
      while(k<m&&idx<n-1){const i0=Math.floor(idx),f=idx-i0;
        const x0=i0<0?rs.last[c]:dv.getInt16((i0*ch+c)*2,true)/32768,x1=dv.getInt16(((i0+1)*ch+c)*2,true)/32768;
        d[k++]=x0+(x1-x0)*f;idx+=ratio}
      if(c===0)rs.newpos=idx-n;rs.last[c]=dv.getInt16(((n-1)*ch+c)*2,true)/32768}
    rs.pos=rs.newpos}
  const now=actx.currentTime;
  if(nextT<now+0.005){nextT=now+lead;if(lead<0.35)lead+=0.03}   /* sous-alimentation : on prend plus de marge */
  else if(nextT>now+lead+0.3){nextT=now+lead}                    /* trop d'avance (rafale réseau) : on resynchronise sans trou */
  const sn=actx.createBufferSource();sn.buffer=ab;sn.connect(actx.destination);sn.start(nextT);nextT+=ab.duration}
function audioWs(){return new Promise(res=>{
  let opened=false,rate=48000,ch=2,hdr=false;
  const ws=new WebSocket((location.protocol==="https:"?"wss://":"ws://")+location.host+"/wsaudio?pin="+encodeURIComponent(PIN));
  wsRef=ws;ws.binaryType="arraybuffer";
  ws.onopen=()=>{opened=true};
  ws.onmessage=e=>{
    if(typeof e.data==="string"){try{const h=JSON.parse(e.data);rate=h.rate;ch=h.ch;hdr=true;nextT=0;lead=0.1;rs=null;
      aud.classList.add("on");aud.textContent="Son temps réel : activé";audSay("Lecture en direct")}catch(x){}return}
    if(hdr&&actx)playChunk(new Uint8Array(e.data),rate,ch)};
  ws.onclose=()=>res(opened?"closed":"failed");
  ws.onerror=()=>{}})}
async function audioLoop(){
  while(audWanted){
    if(!useFetch){
      const r=await audioWs();if(!audWanted)return;
      if(r==="failed"){useFetch=true;audSay("Mode compatible…");continue}
      audSay("Flux interrompu, reconnexion…");await new Promise(res=>{audTimer=setTimeout(res,700)});continue}
    abortC=new AbortController();
    try{
      const r=await fetch("/audio",{headers:{"X-Pin":PIN},signal:abortC.signal});
      if(r.status===401){stopAudio();authFail();return}
      if(r.status!==200){const m=await r.text();audFail("Erreur du PC : "+m);return}
      const rate=+r.headers.get("X-Rate"),ch=+r.headers.get("X-Channels");
      aud.classList.add("on");aud.textContent="Son temps réel : activé";audSay("Lecture en direct");nextT=0;
      const reader=r.body.getReader();let rest=new Uint8Array(0);
      while(audWanted){const {value,done}=await reader.read();if(done)break;
        const buf=new Uint8Array(rest.length+value.length);buf.set(rest);buf.set(value,rest.length);
        const fb=ch*2,usable=buf.length-(buf.length%fb);rest=buf.slice(usable);
        if(usable&&actx)playChunk(buf.subarray(0,usable),rate,ch)}
    }catch(e){if(!audWanted)return}
    if(!audWanted)return;
    audSay("Flux interrompu, reconnexion…");await new Promise(res=>{audTimer=setTimeout(res,1000)})}}
aud.onclick=()=>{
  if(audWanted){stopAudio();return}
  stopBg();audWanted=true;
  try{if(navigator.audioSession)navigator.audioSession.type="playback"}catch(e){}
  actx=new (window.AudioContext||window.webkitAudioContext)({latencyHint:"interactive"});
  actx.resume().catch(()=>{});
  actx.onstatechange=()=>{if(audWanted&&actx&&actx.state!=="running")audSay("Audio "+actx.state+"…")};
  try{silent=new Audio(silentWav());silent.loop=true;silent.play().catch(()=>{})}catch(e){}
  if("mediaSession" in navigator){try{navigator.mediaSession.metadata=new MediaMetadata({title:"Son du PC (temps réel)",artist:"PC Remote"});
    navigator.mediaSession.playbackState="playing";navigator.mediaSession.setActionHandler("pause",()=>stopAudio())}catch(e){}}
  aud.textContent="Son temps réel : connexion…";audSay("Connexion au son du PC…");
  audioLoop()};
function wake(){if(audWanted&&actx&&actx.state!=="running")actx.resume().catch(()=>{});if(audWanted&&silent&&silent.paused)silent.play().catch(()=>{})}
document.addEventListener("visibilitychange",()=>{if(!document.hidden)wake()});window.addEventListener("pageshow",wake);

// Son écran éteint : MP3 en direct dans un lecteur <audio> (continue verrouillé), retard maîtrisé
const bg=document.getElementById("bg"),amsg=document.getElementById("audmsg");
const MMS=window.ManagedMediaSource||window.MediaSource;
let bgEl=null,bgWanted=false,bgRetries=0,bgTimer=null,bgWs=null,bgMS=null,bgSB=null,bgQ=[],bgMode="",bgLag=0,bgTick=null,bgGen=0;
function bgSay(t){amsg.textContent=t||"";amsg.className=""}
function bgFail(t){stopBg();bgSay(t+" (diagnostic : ouvre http://localhost:"+location.port+"/diag sur le PC)");amsg.className="err";
  bg.textContent="Son indisponible : voir le message ci-dessous";setTimeout(()=>{if(!bgWanted)bg.textContent="Son écran éteint"},6000)}
function bgUrl(){return "/stream.mp3?pin="+encodeURIComponent(PIN)+"&t="+Date.now()}
function mseOK(){try{return !!MMS&&MMS.isTypeSupported("audio/mpeg")}catch(e){return false}}
function bgCloseSrc(){try{bgWs&&bgWs.close()}catch(e){}bgWs=null;
  try{if(bgMS&&bgMS.readyState==="open")bgMS.endOfStream()}catch(e){}bgMS=null;bgSB=null;bgQ=[]}
function stopBg(){bgWanted=false;bgGen++;clearTimeout(bgTimer);clearInterval(bgTick);bgTick=null;bgCloseSrc();
  if(bgEl){const a=bgEl;bgEl=null;try{a.pause();a.removeAttribute("src");a.load()}catch(e){}}
  bg.classList.remove("on");bg.textContent="Son écran éteint";bgSay("")}
// Régulateur de retard : mesure l'avance du tampon sur la lecture et la rattrape en douceur
function bgGovern(){
  const a=bgEl;if(!a||!bgWanted)return;
  const b=a.buffered;if(!b.length)return;
  const end=b.end(b.length-1),lag=end-a.currentTime;bgLag=lag;
  if(bgMode==="mse"){
    if(lag>1.2){try{a.currentTime=end-0.45}catch(e){}a.playbackRate=1}
    else if(lag>0.7)a.playbackRate=1.05;
    else if(lag<0.2)a.playbackRate=0.97;
    else a.playbackRate=1;
    if(bgSB&&!bgSB.updating&&b.start(0)<a.currentTime-8){try{bgSB.remove(0,a.currentTime-4)}catch(e){}}
  }else{
    a.playbackRate=lag>6?1.3:lag>3?1.2:lag>1.5?1.1:lag>0.8?1.04:1;
  }
  bgSay("Son écran éteint · décalage ~ "+lag.toFixed(1)+" s ("+(bgMode==="mse"?"direct":"compatible")+")");
}
function bgPump(){
  const sb=bgSB;if(!sb||sb.updating||!bgQ.length)return;
  let n=0;for(const c of bgQ)n+=c.byteLength;
  const b=new Uint8Array(n);let o=0;for(const c of bgQ){b.set(new Uint8Array(c),o);o+=c.byteLength}bgQ=[];
  try{sb.appendBuffer(b)}catch(e){
    if(e&&e.name==="QuotaExceededError"){try{sb.remove(0,Math.max(0,(bgEl?bgEl.currentTime:0)-1))}catch(x){}}
    else bgRetry("Erreur du tampon audio")}}
function bgOpenWs(gen){
  let opened=false;
  const ws=new WebSocket((location.protocol==="https:"?"wss://":"ws://")+location.host+"/wsmp3?pin="+encodeURIComponent(PIN));
  bgWs=ws;ws.binaryType="arraybuffer";
  ws.onopen=()=>{opened=true};
  ws.onmessage=e=>{if(gen!==bgGen||typeof e.data==="string")return;
    bgQ.push(e.data);if(bgQ.length>400)bgQ.splice(0,bgQ.length-100);bgPump()};
  ws.onclose=()=>{if(gen===bgGen&&bgWanted)bgRetry(opened?"Flux interrompu":"Connexion au flux refusée")}}
function bgStartMse(a,gen){
  const ms=new MMS();bgMS=ms;
  if(MMS===window.ManagedMediaSource){try{a.disableRemotePlayback=true}catch(e){}}
  a.src=URL.createObjectURL(ms);
  ms.addEventListener("sourceopen",()=>{
    if(gen!==bgGen)return;
    try{
      const sb=ms.addSourceBuffer("audio/mpeg");try{sb.mode="sequence"}catch(e){}
      bgSB=sb;
      sb.addEventListener("updateend",()=>{bgGovern();bgPump()});
      sb.addEventListener("error",()=>{if(gen===bgGen)bgRetry("Erreur de lecture")});
      bgOpenWs(gen);
    }catch(e){bgFallback(a,"MediaSource refusé")}
  },{once:true});
  const p=a.play();if(p&&p.catch)p.catch(e=>{if(a===bgEl&&e&&e.name==="NotAllowedError")bgFail("Lecture refusée par Safari")})}
function bgStartPlain(a){a.src=bgUrl();const p=a.play();if(p&&p.catch)p.catch(e=>{if(a===bgEl&&e&&e.name==="NotAllowedError")bgFail("Lecture refusée par Safari")})}
function bgStart(a,gen){if(bgMode==="mse")bgStartMse(a,gen);else bgStartPlain(a)}
function bgFallback(a,why){if(a!==bgEl||!bgWanted)return;bgCloseSrc();bgMode="plain";bgGen++;bgSay(why+" : mode compatible…");bgStartPlain(a)}
function bgRetry(why){
  if(!bgWanted||!bgEl)return;
  if(bgRetries>=4){bgFail(why+" : abandon après plusieurs essais");return}
  bgRetries++;bg.classList.remove("on");bg.textContent="Son écran éteint : reconnexion…";bgSay(why+" : reconnexion ("+bgRetries+"/4)…");
  const a=bgEl;bgGen++;const gen=bgGen;bgCloseSrc();clearTimeout(bgTimer);
  bgTimer=setTimeout(()=>{if(bgWanted&&bgEl===a&&gen===bgGen)bgStart(a,gen)},1200)}
function wireBg(a){
  a.addEventListener("playing",()=>{if(a!==bgEl)return;bgRetries=0;bg.classList.add("on");bg.textContent="Son écran éteint : activé"});
  a.addEventListener("waiting",()=>{if(a===bgEl&&bgWanted)bgSay("Mise en mémoire du son…")});
  a.addEventListener("ended",()=>{if(a===bgEl&&bgWanted)bgRetry("Flux terminé")});
  a.addEventListener("error",()=>{if(a!==bgEl||!bgWanted)return;
    if(bgMode==="mse")bgFallback(a,"Lecteur direct indisponible");else bgRetry("Erreur audio (code "+(a.error?a.error.code:0)+")")})}
bg.onclick=()=>{
  if(bgWanted){stopBg();return}
  stopAudio();
  // important sur iPhone : play() doit être appelé directement dans le geste tactile
  bgWanted=true;bgRetries=0;bgGen++;
  const a=new Audio();bgEl=a;wireBg(a);bgMode=mseOK()?"mse":"plain";
  bg.textContent="Son écran éteint : connexion…";bgSay("Connexion au son du PC…");
  bgStart(a,bgGen);
  clearInterval(bgTick);bgTick=setInterval(bgGovern,500);
  if("mediaSession" in navigator){try{navigator.mediaSession.metadata=new MediaMetadata({title:"Son du PC",artist:"PC Remote"});
    navigator.mediaSession.setActionHandler("pause",stopBg)}catch(e){}}
  // vérification côté serveur : affiche la vraie raison en cas de problème
  fetch("/audiocheck",{headers:{"X-Pin":PIN}}).then(async r=>{
    if(a!==bgEl)return;
    if(r.status===401){stopBg();authFail()}
    else if(r.status!==200){const m=await r.text();bgFail("Erreur du PC : "+m)}
  }).catch(()=>{if(a===bgEl){bgFail("PC injoignable : vérifie le Wi-Fi")}})};
document.addEventListener("visibilitychange",()=>{if(!document.hidden&&bgWanted&&bgEl&&bgEl.paused)bgEl.play().catch(()=>{})});

// Mises à jour
const updmsg=document.getElementById("updmsg"),updurl=document.getElementById("updurl");
async function updCall(body){updmsg.textContent="…";try{const r=await fetch("/update",{method:"POST",headers:{"X-Pin":PIN,"Content-Type":"application/json"},body:JSON.stringify(body)});
  updmsg.textContent=r.status===401?"Non connecté":await r.text()}catch(e){updmsg.textContent="PC injoignable"}}
document.getElementById("updgo").onclick=()=>updCall({action:"check"});
document.getElementById("updset").onclick=()=>{const u=updurl.value.trim();if(u)updCall({action:"set",url:u})};
async function pollVersion(){try{const r=await fetch("/version",{cache:"no-store"});const j=await r.json();if(j.build!==BUILD)location.reload()}catch(e){}}
setInterval(pollVersion,3000);

// Téléphone = écran du PC
const scr=document.getElementById("scr"),sImg=document.getElementById("scrImg");
let screenOn=false,dragMode=false,rightNext=false,sDown=false,lpT=null,lpFired=false,sMoved=0,sTwo=false,sT0=0,lx=0,ly=0,ssy=0;
function isRemote(){return !/^(192\.168\.|10\.|172\.(1[6-9]|2\d|3[01])\.|127\.|localhost)/.test(location.hostname)}
let lite=false;try{const v=localStorage.getItem("lite");lite=v===null?isRemote():v==="1"}catch(e){lite=isRemote()}
function screenUrl(){return "/screen?pin="+encodeURIComponent(PIN)+(lite?"&lite=1":"")+"&t="+Date.now()}
function openScreen(){screenOn=true;scr.style.display="block";setFull(true);wakeOn();sImg.src=screenUrl()}
function closeScreen(){screenOn=false;wakeOff();try{setFull(false)}catch(e){}sImg.removeAttribute("src");scr.style.display="none"}
document.getElementById("scrBtn").onclick=openScreen;
document.getElementById("sBack").onclick=closeScreen;
sImg.onerror=()=>{if(screenOn){closeScreen();alert("Impossible d'afficher l'écran : vérifie le PIN et relance lancer.bat (module Pillow).")}};
document.getElementById("sKb").onclick=()=>document.getElementById("sIn").focus();
const bDrag=document.getElementById("sDrag"),bRight=document.getElementById("sRight");
bDrag.onclick=()=>{dragMode=!dragMode;bDrag.classList.toggle("on",dragMode)};
bRight.onclick=()=>{rightNext=!rightNext;bRight.classList.toggle("on",rightNext)};
function setFull(f){scr.classList.toggle("full",f);if(f){try{const fs=scr.requestFullscreen||scr.webkitRequestFullscreen;if(fs&&!document.fullscreenElement&&!document.webkitFullscreenElement){const r=fs.call(scr);if(r&&r.catch)r.catch(()=>{})}}catch(e){}}else{try{if(document.fullscreenElement&&document.exitFullscreen)document.exitFullscreen();else if(document.webkitFullscreenElement&&document.webkitExitFullscreen)document.webkitExitFullscreen()}catch(e){}}}
document.getElementById("sMore").onclick=()=>setFull(true);
let wl=null;async function wakeOn(){try{if(navigator.wakeLock&&screenOn&&!wl){wl=await navigator.wakeLock.request("screen");wl.addEventListener("release",()=>{wl=null})}}catch(e){wl=null}}
function wakeOff(){try{if(wl){wl.release();wl=null}}catch(e){wl=null}}
document.addEventListener("visibilitychange",()=>{if(document.visibilityState==="visible"&&screenOn){sImg.src=screenUrl();wakeOn()}});
document.getElementById("sKT").onclick=()=>document.getElementById("sIn").focus();
["sTab","sKT"].forEach(i=>document.getElementById(i).addEventListener("touchstart",e=>e.stopPropagation(),{passive:true}));
document.getElementById("sTab").onclick=()=>setFull(false);
document.getElementById("sTab").addEventListener("touchstart",e=>e.stopPropagation(),{passive:true});
function norm(t){const r=sImg.getBoundingClientRect(),nw=sImg.naturalWidth||r.width,nh=sImg.naturalHeight||r.height;
  const sc=Math.min(r.width/nw,r.height/nh),w=nw*sc,h=nh*sc,l=r.left+(r.width-w)/2,tp=r.top+(r.height-h)/2;
  return {x:Math.min(1,Math.max(0,(t.clientX-l)/w)),y:Math.min(1,Math.max(0,(t.clientY-tp)/h))}}
function absMove(t){const p=norm(t);ev({t:"a",x:p.x,y:p.y})}
function endPress(){clearTimeout(lpT);lpT=null}
sImg.addEventListener("touchstart",e=>{e.preventDefault();const t=e.touches;
  if(t.length===1){sMoved=0;sTwo=false;lpFired=false;sT0=Date.now();lx=t[0].clientX;ly=t[0].clientY;absMove(t[0]);
    if(dragMode){ev({t:"d",b:"l"});sDown=true}
    else{lpT=setTimeout(()=>{if(sMoved<10&&!sTwo){lpFired=true;ev({t:"c",b:"r"})}},550)}}
  else{sTwo=true;endPress();ly=t[0].clientY;ssy=0}},{passive:false});
sImg.addEventListener("touchmove",e=>{e.preventDefault();const t=e.touches;
  const x=t[0].clientX,y=t[0].clientY;sMoved+=Math.abs(x-lx)+Math.abs(y-ly);
  if(t.length>=2){ssy+=(y-ly)/12;const n=Math.trunc(ssy);if(n){ev({t:"s",n:n});ssy-=n}}
  else if(!sTwo){absMove(t[0]);if(sMoved>=10)endPress()}
  lx=x;ly=y},{passive:false});
sImg.addEventListener("touchend",e=>{e.preventDefault();
  if(e.touches.length===0){endPress();
    if(sDown){ev({t:"u",b:"l"});sDown=false}
    else if(!lpFired&&sMoved<10&&Date.now()-sT0<500){
      const b=(sTwo||rightNext)?"r":"l";ev({t:"c",b:b});
      if(rightNext){rightNext=false;bRight.classList.remove("on")}}}},{passive:false});
sImg.addEventListener("touchcancel",()=>{endPress();if(sDown){ev({t:"u",b:"l"});sDown=false}});

// Pavé tactile
const pad=document.getElementById("pad");
let last=null,t0=0,moved=0,rx=0,ry=0,sy=0,lastTap=0,dragging=false,two=false;
pad.addEventListener("touchstart",e=>{e.preventDefault();const t=e.touches;
  if(t.length===1){last={x:t[0].clientX,y:t[0].clientY};t0=Date.now();moved=0;two=false;rx=ry=0;
    if(Date.now()-lastTap<300){dragging=true;ev({t:"d",b:"l"})}}
  else{two=true;last={x:t[0].clientX,y:t[0].clientY};sy=0}},{passive:false});
pad.addEventListener("touchmove",e=>{e.preventDefault();const t=e.touches;if(!last)return;
  const x=t[0].clientX,y=t[0].clientY,dx=x-last.x,dy=y-last.y;last={x:x,y:y};moved+=Math.abs(dx)+Math.abs(dy);
  if(t.length>=2){sy+=dy/12;const n=Math.trunc(sy);if(n){ev({t:"s",n:n});sy-=n}}
  else if(!two){rx+=dx*SENS;ry+=dy*SENS;const ix=Math.trunc(rx),iy=Math.trunc(ry);rx-=ix;ry-=iy;if(ix||iy)ev({t:"m",x:ix,y:iy})}},{passive:false});
pad.addEventListener("touchend",e=>{e.preventDefault();
  if(e.touches.length===0){
    if(dragging){ev({t:"u",b:"l"});dragging=false}
    else if(moved<8&&Date.now()-t0<250){ev({t:"c",b:two?"r":"l"});if(!two)lastTap=Date.now()}}},{passive:false});
pad.addEventListener("touchcancel",()=>{if(dragging){ev({t:"u",b:"l"});dragging=false}});

// Saisie de texte (espace "sentinelle" pour détecter les suppressions)
function wireInput(inp){let busy=false;inp.value=" ";
  inp.addEventListener("input",()=>{if(busy)return;const v=inp.value;
    if(v.length<1)key(8);else if(v.length>1)ev({t:"txt",s:v.slice(1),mods:takeMods()});
    busy=true;inp.value=" ";busy=false});
  inp.addEventListener("keydown",e=>{if(e.key==="Enter"){e.preventDefault();key(13)}})}
wireInput(document.getElementById("in"));wireInput(document.getElementById("sIn"));

// Alimentation
function askYes(txt){return new Promise(res=>{const c=document.getElementById("conf");document.getElementById("ctxt").textContent=txt;c.classList.add("on");
  const done=v=>{c.classList.remove("on");res(v)};document.getElementById("cYes").onclick=()=>done(true);document.getElementById("cNo").onclick=()=>done(false)})}
const pmsg=document.getElementById("pmsg");
async function power(a,q,ok){if(q&&!(await askYes(q)))return;
  try{const r=await fetch("/power",{method:"POST",headers:{"X-Pin":PIN,"Content-Type":"application/json"},body:JSON.stringify({action:a})});
    pmsg.textContent=r.ok?ok:"Échec ("+r.status+")"}catch(e){pmsg.textContent="PC injoignable."}}
document.getElementById("pOff").onclick=()=>power("shutdown","Éteindre le PC ? Il s'éteint dans 15 secondes (tu peux annuler).","Extinction dans 15 s. Touche « Annuler l'extinction » pour l'arrêter.");
document.getElementById("pRst").onclick=()=>power("restart","Redémarrer le PC ? Le contrôle sera coupé quelques minutes.","Redémarrage dans 15 s.");
document.getElementById("pSlp").onclick=()=>power("sleep","Mettre le PC en veille ? Le contrôle sera coupé.","Mise en veille...");
document.getElementById("pLck").onclick=()=>power("lock","","PC verrouillé.");
document.getElementById("pCan").onclick=()=>power("cancel","","Extinction annulée (si elle était en cours).");
document.getElementById("pOn").onclick=async()=>{pmsg.textContent="...";try{const r=await fetch("/wakeinfo",{headers:{"X-Pin":PIN}});const j=await r.json();
  pmsg.textContent="Un PC éteint ne peut pas être réveillé depuis cette page (Safari ne sait pas envoyer le signal de réveil).\n\nPour l'allumer : applique le réveil réseau (voir LISEZMOI), puis envoie un « Wake on LAN » depuis l'iPhone avec cette adresse :\n\nMAC : "+j.mac+"\nIP : "+j.ip+"\nNom : "+j.name+"\nPort : 9"}catch(e){pmsg.textContent="PC injoignable : note l'adresse MAC pendant que le PC est allumé."}};

// Accès à distance
const liteBox=document.getElementById("lite");liteBox.checked=lite;
liteBox.onchange=()=>{lite=liteBox.checked;try{localStorage.setItem("lite",lite?"1":"0")}catch(e){}if(screenOn)sImg.src=screenUrl()};
document.getElementById("rem").addEventListener("toggle",async e=>{if(!e.target.open)return;const m=document.getElementById("rmsg");
  try{const r=await fetch("/wakeinfo",{headers:{"X-Pin":PIN}});const j=await r.json();
    m.textContent=(isRemote()?"Tu es connecté à distance.\n":"Tu es sur le Wi-Fi de la maison.\n")+(j.ts?"Adresse à distance (Tailscale) :\nhttp://"+j.ts+":"+location.port+"\nGarde Tailscale actif sur l'iPhone.":"À distance : pas activé. Lance acces_distance.bat sur le PC (voir LISEZMOI).")}catch(err){m.textContent="PC injoignable."}});
</script></body></html>
"""

# ---------------- Polices (Press Start 2P, VT323, Bangers : licence OFL) ----------------
FONTS_B64 = {
    "ps2p": "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",
    "vt323": "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",
    "bangers": "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",
}
FONTS = {k: base64.b64decode(v) for k, v in FONTS_B64.items()}
ICON = base64.b64decode("iVBORw0KGgoAAAANSUhEUgAAALQAAAC0CAIAAACyr5FlAAAB00lEQVR42u3dwa6CMBCGUTC+/yvXvdRESYX523OWd6XcL0MmWN02AACAivbjn1prrsuKKezvMTxcFD4RB+JAHIgDcSAOxIE4EAfiQBwgDsSBOBAH4kAciANxIA7EAeJAHIgDcSAOanhGvMrjMc4t50xv7os3ORAH4kAciANxYJU9r7v4FVwRo1dukwNxIA7EgTgQB1bZyffbybZWkwNxIA7EgTgQB1bZqfbbFbZWkwNxIA7EgTgQB0HuXNK6KyJ1/h0mB24riANxIA7EQU0XPZVd9sFm9KUzORAH4kAciANxIA7EgTgQB+IAcSAOBgg+K/v955MLfmTaj/HgtoI4EAeIA3Ew+Spb8FTtCgd9TQ7EgTgQB+JAHIgDcSAOxIE4QByIgwEynsoW/DiuH+PBbQXEgTgQB+LAKvuzgt+KPNkXNZsciANxIA7EgTiwyg7WXRHvPcI62aNakwNxIA7EgTgQB1ZZy6TJgTgQB+IAcSAOclbZgk9QLecmB+JAHIgDcSAOrLJX77cpD2Bz35HJgTgQB+JAHIiDontW7orIv1dukwO3FcSBOBAH4kAciANxIA7EAeJAHIgDcSAOxIE4EAfiQBwgDsSBOBAH4kAcAAAAcMILCk1eU8TvJdoAAAAASUVORK5CYII=")


if __name__ == "__main__":
    if IS_WIN:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass
    srv = None
    first_port = PORT
    for _port in range(first_port, first_port + 10):
        try:
            srv = ThreadingHTTPServer(("0.0.0.0", _port), H)
            PORT = _port
            break
        except OSError:
            continue
    if srv is None:
        print("ERREUR : les ports %d a %d sont deja utilises. Ferme les autres fenetres PC Remote puis relance." % (first_port, first_port + 9))
        sys.exit(1)
    if PORT != first_port:
        print("ATTENTION : le port %d est deja utilise (une autre fenetre PC Remote est peut-etre ouverte). Port utilise : %d" % (first_port, PORT))
    srv.daemon_threads = True
    ip = local_ip()
    print("=" * 50)
    print(" PC Remote Wi-Fi %s est lance" % VERSION)
    print(" Sur l'iPhone (meme Wi-Fi), ouvre Safari et va sur :")
    print("     http://%s:%d" % (ip, PORT))
    print(" Code PIN a saisir sur l'iPhone :  %s" % PIN)
    print(" Lien direct (PIN inclus) : http://%s:%d/?pin=%s" % (ip, PORT, PIN))
    tsip = tailscale_ip()
    if tsip:
        print(" A distance (Tailscale) : http://%s:%d/?pin=%s" % (tsip, PORT, PIN))
    else:
        print(" A distance : pas active (voir acces_distance.bat)")
    print(" Un QR code va s'ouvrir sur le PC : scanne-le avec l'iPhone.")
    print(" Probleme de son ? Ouvre sur le PC : http://localhost:%d/diag" % PORT)
    print(" Ctrl+C pour arreter")
    print("=" * 50)
    if not IS_WIN:
        print("(mode test : pas Windows, les actions sont seulement affichees)")
    threading.Thread(target=updater_loop, daemon=True).start()
    if IS_WIN and not RESTARTED:
        threading.Timer(1.0, lambda: webbrowser.open("http://localhost:%d/qr" % PORT)).start()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("Arret.")
