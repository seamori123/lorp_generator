#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Генератор линейной однородной рекуррентной последовательности максимального периода.

Задача: по примарному числу q = p^m и натуральному k построить ЛОРП порядка k
над полем GF(q) с максимально возможным минимальным периодом q^k - 1.

Запуск:
    python lorp_max_period_gui.py

Зависимости: только стандартная библиотека Python 3.9+.
"""

import itertools
import threading
import time
import tkinter as tk
from tkinter import ttk, messagebox


# -----------------------------------------------------------------------------
# Ограничения программы
# -----------------------------------------------------------------------------

MAX_Q = 121                 # q не больше 121, чтобы не раздувать поле и таблицы
MAX_K = 6                   # порядок рекурсии не больше 6
MAX_CANDIDATES = 250_000    # максимум кандидатов характеристического многочлена
MAX_PERIOD_TO_BUILD = 80_000
SMALL_FIELD_TABLE_Q = 16    # таблицу элементов поля показываем только для малых q
DEFAULT_TIMEOUT = 20.0


# -----------------------------------------------------------------------------
# Простые числа и примарные числа
# -----------------------------------------------------------------------------

def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def prime_power(q: int):
    """Возвращает (p, m), если q = p^m, иначе None."""
    if q < 2:
        return None
    if is_prime(q):
        return q, 1
    for p in range(2, int(q ** 0.5) + 1):
        if is_prime(p) and q % p == 0:
            cur = q
            m = 0
            while cur % p == 0:
                cur //= p
                m += 1
            if cur == 1:
                return p, m
            return None
    return None


def prime_divisors(n: int) -> list[int]:
    result = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            result.append(d)
            while n % d == 0:
                n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        result.append(n)
    return result


# -----------------------------------------------------------------------------
# Многочлены над простым полем GF(p)
# -----------------------------------------------------------------------------

def trim(poly: list[int], p: int) -> list[int]:
    poly = [x % p for x in poly]
    while poly and poly[-1] == 0:
        poly.pop()
    return poly


def poly_add_fp(a, b, p):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)], p)


def poly_sub_fp(a, b, p):
    n = max(len(a), len(b))
    return trim([(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)], p)


def poly_mul_fp(a, b, p):
    if not a or not b:
        return []
    c = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            c[i + j] += ai * bj
    return trim(c, p)


def poly_divmod_fp(a, b, p):
    a = trim(a[:], p)
    b = trim(b[:], p)
    if not b:
        raise ZeroDivisionError("деление на нулевой многочлен")
    if len(a) < len(b):
        return [], a

    q = [0] * (len(a) - len(b) + 1)
    r = a[:]
    inv_lc = pow(b[-1], -1, p)

    for shift in range(len(a) - len(b), -1, -1):
        pos = shift + len(b) - 1
        if r[pos] == 0:
            continue
        coef = r[pos] * inv_lc % p
        q[shift] = coef
        for j in range(len(b)):
            r[shift + j] = (r[shift + j] - coef * b[j]) % p

    return trim(q, p), trim(r, p)


def poly_mod_fp(a, mod, p):
    return poly_divmod_fp(a, mod, p)[1]


def poly_gcd_fp(a, b, p):
    a = trim(a[:], p)
    b = trim(b[:], p)
    while b:
        _, r = poly_divmod_fp(a, b, p)
        a, b = b, r
    if a and a[-1] != 1:
        inv = pow(a[-1], -1, p)
        a = trim([x * inv for x in a], p)
    return a


def poly_pow_mod_fp(base, degree: int, mod, p):
    res = [1]
    cur = poly_mod_fp(base, mod, p)
    while degree:
        if degree & 1:
            res = poly_mod_fp(poly_mul_fp(res, cur, p), mod, p)
        cur = poly_mod_fp(poly_mul_fp(cur, cur, p), mod, p)
        degree >>= 1
    return res


def poly_derivative_fp(f, p):
    if len(f) <= 1:
        return []
    return trim([(i * f[i]) % p for i in range(1, len(f))], p)


def irreducible_over_fp(f, p) -> bool:
    """Проверка неприводимости многочлена над GF(p)."""
    deg = len(f) - 1
    if deg <= 0:
        return False

    der = poly_derivative_fp(f, p)
    if der and len(poly_gcd_fp(f, der, p)) > 1:
        return False

    x = [0, 1]
    h = x[:]
    for i in range(1, deg + 1):
        h = poly_pow_mod_fp(h, p, f, p)
        if i < deg and len(poly_gcd_fp(f, poly_sub_fp(h, x, p), p)) > 1:
            return False
    return h == x


def find_irreducible_for_field(p: int, m: int, timeout=DEFAULT_TIMEOUT):
    """Ищет унитарный неприводимый многочлен степени m над GF(p)."""
    if m == 1:
        return [0, 1]
    started = time.monotonic()
    for coeffs in itertools.product(range(p), repeat=m):
        if time.monotonic() - started > timeout:
            raise TimeoutError("слишком долго ищется неприводимый многочлен поля")
        f = list(coeffs) + [1]
        if irreducible_over_fp(f, p):
            return f
    raise RuntimeError("не удалось построить расширенное поле")


# -----------------------------------------------------------------------------
# Конечное поле GF(p^m)
# -----------------------------------------------------------------------------

class FiniteField:
    """
    Поле GF(q), где q = p^m.

    Если m = 1, элемент поля — обычное число 0..p-1.
    Если m > 1, элемент хранится как код числа:
        code = a0 + a1*p + a2*p^2 + ... + a_{m-1}*p^{m-1}.

    Этому коду соответствует многочлен:
        a0 + a1*α + a2*α^2 + ... + a_{m-1}*α^{m-1},
    где α — корень выбранного неприводимого многочлена степени m над GF(p).
    """

    def __init__(self, p: int, m: int):
        self.p = p
        self.m = m
        self.q = p ** m
        self.mod_poly = None if m == 1 else find_irreducible_for_field(p, m)

    def to_vector(self, a: int) -> list[int]:
        a %= self.q
        if self.m == 1:
            return [a]
        v = []
        for _ in range(self.m):
            v.append(a % self.p)
            a //= self.p
        return v

    def from_vector(self, v: list[int]) -> int:
        if self.m == 1:
            return (v[0] if v else 0) % self.p
        code = 0
        base = 1
        for x in v[:self.m]:
            code += (x % self.p) * base
            base *= self.p
        return code % self.q

    def _reduce(self, f: list[int]) -> list[int]:
        if self.m == 1:
            return [f[0] % self.p] if f else [0]
        return poly_mod_fp(f, self.mod_poly, self.p) or [0]

    def add(self, a, b):
        if self.m == 1:
            return (a + b) % self.p
        return self.from_vector(poly_add_fp(self.to_vector(a), self.to_vector(b), self.p))

    def sub(self, a, b):
        if self.m == 1:
            return (a - b) % self.p
        return self.from_vector(poly_sub_fp(self.to_vector(a), self.to_vector(b), self.p))

    def neg(self, a):
        return self.sub(0, a)

    def mul(self, a, b):
        if self.m == 1:
            return (a * b) % self.p
        prod = poly_mul_fp(self.to_vector(a), self.to_vector(b), self.p)
        return self.from_vector(self._reduce(prod))

    def inv(self, a):
        if a == 0:
            raise ZeroDivisionError("у нуля нет обратного элемента")
        if self.m == 1:
            return pow(a, -1, self.p)

        r0 = self.mod_poly[:]
        r1 = trim(self.to_vector(a), self.p)
        s0 = []
        s1 = [1]

        while r1:
            q, r2 = poly_divmod_fp(r0, r1, self.p)
            r0, r1 = r1, r2
            s0, s1 = s1, poly_sub_fp(s0, poly_mul_fp(q, s1, self.p), self.p)

        inv_lc = pow(r0[-1], -1, self.p)
        s0 = trim([x * inv_lc for x in s0], self.p)
        return self.from_vector(self._reduce(s0))

    def scalar_mul(self, n: int, a: int) -> int:
        n %= self.p
        res = 0
        for _ in range(n):
            res = self.add(res, a)
        return res

    def element_as_vector(self, a: int) -> str:
        if self.m == 1:
            return str(a % self.p)
        return "(" + ", ".join(map(str, self.to_vector(a))) + ")"

    def element_as_poly(self, a: int) -> str:
        if self.m == 1:
            return str(a % self.p)
        parts = []
        for i, c in enumerate(self.to_vector(a)):
            if c == 0:
                continue
            if i == 0:
                parts.append(str(c))
            elif i == 1:
                parts.append("α" if c == 1 else f"{c}α")
            else:
                parts.append(f"α^{i}" if c == 1 else f"{c}α^{i}")
        return " + ".join(parts) if parts else "0"

    def element_to_text(self, a: int, mode: str) -> str:
        if mode == "poly":
            return self.element_as_poly(a)
        if mode == "code":
            return str(a)
        return self.element_as_vector(a)

    def field_explanation(self) -> str:
        lines = []
        lines.append(f"Поле: GF({self.q}) = GF({self.p}^{self.m}).")
        if self.m == 1:
            lines.append(f"Так как m = 1, поле простое: элементы — числа 0, 1, ..., {self.p - 1}; операции выполняются по модулю {self.p}.")
            return "\n".join(lines)

        lines.append("Поле расширенное, поэтому элемент поля записывается вектором коэффициентов:")
        lines.append(f"    (a0, a1, ..., a{self.m - 1}), где каждый ai принадлежит GF({self.p}).")
        lines.append("Вектор означает многочлен:")
        lines.append(f"    a0 + a1·α + ... + a{self.m - 1}·α^{self.m - 1}.")
        lines.append("Числовой код элемента нужен только для хранения в программе:")
        lines.append(f"    code = a0 + a1·{self.p} + ... + a{self.m - 1}·{self.p}^{self.m - 1}.")
        lines.append(f"α — корень неприводимого многочлена: {poly_text_fp(self.mod_poly, 't')}.")

        example = min(self.q - 1, sum(self.p ** i for i in range(self.m)))
        lines.append(f"Пример: код {example} = {self.element_as_vector(example)} = {self.element_as_poly(example)}.")

        if self.q <= SMALL_FIELD_TABLE_Q:
            lines.append("\nНебольшая таблица элементов поля:")
            lines.append(" код | вектор | многочлен")
            lines.append("-----+--------+----------")
            for a in range(self.q):
                lines.append(f" {a:>3} | {self.element_as_vector(a):>6} | {self.element_as_poly(a)}")
        else:
            lines.append(f"Таблица всех {self.q} элементов не выводится, чтобы не перегружать результат.")
        return "\n".join(lines)


# -----------------------------------------------------------------------------
# Многочлены над GF(q)
# -----------------------------------------------------------------------------

class PolyGF:
    def __init__(self, field: FiniteField):
        self.F = field

    def norm(self, a):
        a = [x % self.F.q for x in a]
        while a and a[-1] == 0:
            a.pop()
        return a

    def add(self, a, b):
        n = max(len(a), len(b))
        return self.norm([self.F.add(a[i] if i < len(a) else 0, b[i] if i < len(b) else 0) for i in range(n)])

    def sub(self, a, b):
        n = max(len(a), len(b))
        return self.norm([self.F.sub(a[i] if i < len(a) else 0, b[i] if i < len(b) else 0) for i in range(n)])

    def mul(self, a, b):
        if not a or not b:
            return []
        c = [0] * (len(a) + len(b) - 1)
        for i, ai in enumerate(a):
            if ai == 0:
                continue
            for j, bj in enumerate(b):
                if bj != 0:
                    c[i + j] = self.F.add(c[i + j], self.F.mul(ai, bj))
        return self.norm(c)

    def divmod(self, a, b):
        a = self.norm(a[:])
        b = self.norm(b[:])
        if not b:
            raise ZeroDivisionError("деление на нулевой многочлен")
        if len(a) < len(b):
            return [], a

        q = [0] * (len(a) - len(b) + 1)
        r = a[:]
        inv_lc = self.F.inv(b[-1])

        for shift in range(len(a) - len(b), -1, -1):
            pos = shift + len(b) - 1
            if r[pos] == 0:
                continue
            coef = self.F.mul(r[pos], inv_lc)
            q[shift] = coef
            for j in range(len(b)):
                r[shift + j] = self.F.sub(r[shift + j], self.F.mul(coef, b[j]))

        return self.norm(q), self.norm(r)

    def mod(self, a, b):
        return self.divmod(a, b)[1]

    def gcd(self, a, b):
        a = self.norm(a[:])
        b = self.norm(b[:])
        while b:
            _, r = self.divmod(a, b)
            a, b = b, r
        if a and a[-1] != 1:
            inv = self.F.inv(a[-1])
            a = self.norm([self.F.mul(x, inv) for x in a])
        return a

    def pow_mod(self, base, exp, mod_poly):
        res = [1]
        cur = self.mod(base, mod_poly)
        while exp:
            if exp & 1:
                res = self.mod(self.mul(res, cur), mod_poly)
            cur = self.mod(self.mul(cur, cur), mod_poly)
            exp >>= 1
        return res

    def derivative(self, f):
        if len(f) <= 1:
            return []
        return self.norm([self.F.scalar_mul(i, f[i]) for i in range(1, len(f))])


def irreducible_over_field(f, F: FiniteField) -> bool:
    deg = len(f) - 1
    if deg <= 0:
        return False
    pg = PolyGF(F)
    der = pg.derivative(f)
    if der and len(pg.gcd(f, der)) > 1:
        return False

    x = [0, 1]
    h = x[:]
    for i in range(1, deg + 1):
        h = pg.pow_mod(h, F.q, f)
        if i < deg and len(pg.gcd(f, pg.sub(h, x))) > 1:
            return False
    return h == x


def primitive_over_field(f, F: FiniteField) -> bool:
    if not irreducible_over_field(f, F):
        return False
    deg = len(f) - 1
    order = F.q ** deg - 1
    pg = PolyGF(F)
    x = [0, 1]

    if pg.pow_mod(x, order, f) != [1]:
        return False
    for r in prime_divisors(order):
        if pg.pow_mod(x, order // r, f) == [1]:
            return False
    return True


def find_primitive_polynomial(F: FiniteField, k: int, progress=None, timeout=DEFAULT_TIMEOUT):
    started = time.monotonic()
    checked = 0
    candidates_total = (F.q - 1) * (F.q ** (k - 1))

    if candidates_total > MAX_CANDIDATES:
        raise ValueError(
            f"слишком много кандидатов для перебора: {candidates_total}. "
            f"В программе ограничение MAX_CANDIDATES = {MAX_CANDIDATES}."
        )

    for coeffs in itertools.product(range(F.q), repeat=k):
        if coeffs[0] == 0:
            continue
        if time.monotonic() - started > timeout:
            raise TimeoutError("поиск примитивного характеристического многочлена превысил лимит времени")
        checked += 1
        f = list(coeffs) + [1]
        if primitive_over_field(f, F):
            return f, checked, candidates_total
        if progress and checked % 300 == 0:
            progress(f"Проверено {checked} из {candidates_total} кандидатов...")

    raise RuntimeError("примитивный многочлен не найден")


# -----------------------------------------------------------------------------
# Последовательность
# -----------------------------------------------------------------------------

def build_sequence(F: FiniteField, characteristic: list[int], init: list[int], total: int):
    k = len(init)
    rec = [F.neg(characteristic[i]) for i in range(k)]
    state = init[:]
    seq = state[:]

    while len(seq) < total:
        nxt = 0
        for i in range(k):
            nxt = F.add(nxt, F.mul(rec[i], state[i]))
        state = state[1:] + [nxt]
        seq.append(nxt)

    return seq[:total], state


def recurrence_text(F: FiniteField, f: list[int]) -> str:
    k = len(f) - 1
    parts = []
    for i in range(k):
        c = F.neg(f[i])
        if c == 0:
            continue
        idx = "n" if i == 0 else f"n+{i}"
        parts.append(f"({F.element_as_poly(c)})·s[{idx}]")
    right = " + ".join(parts) if parts else "0"
    return f"s[n+{k}] = {right}"


def poly_text_fp(f: list[int], var='x') -> str:
    if not f:
        return "0"
    parts = []
    for i, c in enumerate(f):
        if c == 0:
            continue
        if i == 0:
            parts.append(str(c))
        elif i == 1:
            parts.append(var if c == 1 else f"{c}{var}")
        else:
            parts.append(f"{var}^{i}" if c == 1 else f"{c}{var}^{i}")
    return " + ".join(parts) if parts else "0"


def poly_text_field(f: list[int], F: FiniteField, var='x') -> str:
    parts = []
    for i, c in enumerate(f):
        if c == 0:
            continue
        cs = F.element_as_poly(c)
        if i == 0:
            parts.append(cs)
        elif i == 1:
            parts.append(var if c == 1 else f"({cs}){var}")
        else:
            parts.append(f"{var}^{i}" if c == 1 else f"({cs}){var}^{i}")
    return " + ".join(parts) if parts else "0"


def validate_limits(q: int, k: int):
    if q > MAX_Q:
        raise ValueError(f"q слишком большое. В этой версии q ≤ {MAX_Q}.")
    if k > MAX_K:
        raise ValueError(f"k слишком большое. В этой версии k ≤ {MAX_K}.")
    candidates = (q - 1) * (q ** (k - 1))
    if candidates > MAX_CANDIDATES:
        raise ValueError(
            f"пара q={q}, k={k} даёт {candidates} кандидатов. "
            f"Разрешено не больше {MAX_CANDIDATES}."
        )


# -----------------------------------------------------------------------------
# GUI
# -----------------------------------------------------------------------------

class App:
    def __init__(self, root):
        self.root = root
        self.root.title("ЛОРП максимального периода над GF(q)")
        self.root.geometry("980x760")
        self.root.minsize(820, 620)
        self.last_result = None
        self.stop = False
        self._make_widgets()

    def _make_widgets(self):
        top = ttk.LabelFrame(self.root, text="Параметры", padding=10)
        top.pack(fill=tk.X, padx=10, pady=8)

        ttk.Label(top, text="q = p^m:").grid(row=0, column=0, sticky="w")
        self.q_var = tk.StringVar(value="4")
        ttk.Entry(top, textvariable=self.q_var, width=10).grid(row=0, column=1, padx=6)

        ttk.Label(top, text="k:").grid(row=0, column=2, sticky="w")
        self.k_var = tk.StringVar(value="3")
        ttk.Entry(top, textvariable=self.k_var, width=10).grid(row=0, column=3, padx=6)

        ttk.Label(top, text="Показать элементов:").grid(row=0, column=4, sticky="w")
        self.count_var = tk.StringVar(value="200")
        ttk.Entry(top, textvariable=self.count_var, width=10).grid(row=0, column=5, padx=6)

        self.full_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(top, text="показать весь период", variable=self.full_var).grid(row=0, column=6, padx=8)

        self.mode_var = tk.StringVar(value="vector")
        ttk.Label(top, text="Вид: ").grid(row=1, column=0, pady=(8, 0), sticky="w")
        ttk.Radiobutton(top, text="вектор", variable=self.mode_var, value="vector", command=self.redraw).grid(row=1, column=1, sticky="w", pady=(8, 0))
        ttk.Radiobutton(top, text="многочлен", variable=self.mode_var, value="poly", command=self.redraw).grid(row=1, column=2, sticky="w", pady=(8, 0))
        ttk.Radiobutton(top, text="код", variable=self.mode_var, value="code", command=self.redraw).grid(row=1, column=3, sticky="w", pady=(8, 0))

        self.start_btn = ttk.Button(top, text="Сгенерировать", command=self.start)
        self.start_btn.grid(row=1, column=4, padx=6, pady=(8, 0), sticky="ew")
        self.stop_btn = ttk.Button(top, text="Стоп", state=tk.DISABLED, command=self.stop_calc)
        self.stop_btn.grid(row=1, column=5, padx=6, pady=(8, 0), sticky="ew")

        info = (
            f"Ограничения: q ≤ {MAX_Q}, k ≤ {MAX_K}, кандидатов ≤ {MAX_CANDIDATES}. "
            "Для больших q и k перебор примитивного многочлена становится слишком долгим."
        )
        ttk.Label(top, text=info, foreground="#666666").grid(row=2, column=0, columnspan=7, sticky="w", pady=(8, 0))

        self.status = tk.StringVar(value="Готово")
        ttk.Label(self.root, textvariable=self.status, relief=tk.SUNKEN, anchor="w").pack(fill=tk.X, padx=10)
        self.progress = ttk.Progressbar(self.root, mode="indeterminate")
        self.progress.pack(fill=tk.X, padx=10, pady=(2, 8))

        out_frame = ttk.LabelFrame(self.root, text="Результат", padding=8)
        out_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))

        self.text = tk.Text(out_frame, wrap=tk.NONE, font=("Consolas", 11), padx=8, pady=8)
        self.text.grid(row=0, column=0, sticky="nsew")
        y = ttk.Scrollbar(out_frame, orient=tk.VERTICAL, command=self.text.yview)
        x = ttk.Scrollbar(out_frame, orient=tk.HORIZONTAL, command=self.text.xview)
        y.grid(row=0, column=1, sticky="ns")
        x.grid(row=1, column=0, sticky="ew")
        self.text.configure(yscrollcommand=y.set, xscrollcommand=x.set)
        out_frame.rowconfigure(0, weight=1)
        out_frame.columnconfigure(0, weight=1)
        self.text.configure(state=tk.DISABLED)

    def set_text(self, s: str):
        self.text.configure(state=tk.NORMAL)
        self.text.delete("1.0", tk.END)
        self.text.insert(tk.END, s)
        self.text.configure(state=tk.DISABLED)

    def stop_calc(self):
        self.stop = True
        self.status.set("Остановка...")

    def start(self):
        try:
            q = int(self.q_var.get())
            k = int(self.k_var.get())
            pp = prime_power(q)
            if pp is None:
                raise ValueError("q должно быть примарным числом: q = p^m, где p — простое, m ≥ 1")
            if k < 1:
                raise ValueError("k должно быть натуральным числом")
            validate_limits(q, k)
        except Exception as e:
            messagebox.showerror("Ошибка ввода", str(e))
            return

        self.stop = False
        self.start_btn.configure(state=tk.DISABLED)
        self.stop_btn.configure(state=tk.NORMAL)
        self.progress.start()
        self.set_text("")

        thread = threading.Thread(target=self.worker, args=(q, k, pp), daemon=True)
        thread.start()

    def progress_msg(self, s):
        if self.stop:
            raise InterruptedError("вычисление прервано")
        self.root.after(0, lambda: self.status.set(s))

    def worker(self, q, k, pp):
        try:
            p, m = pp
            self.progress_msg("Строится поле GF(q)...")
            F = FiniteField(p, m)

            self.progress_msg("Ищется примитивный характеристический многочлен...")
            f, checked, total = find_primitive_polynomial(F, k, self.progress_msg)

            period = q ** k - 1
            if self.full_var.get():
                if period > MAX_PERIOD_TO_BUILD:
                    raise ValueError(
                        f"Весь период содержит {period} элементов. "
                        f"В этой версии целиком можно строить не больше {MAX_PERIOD_TO_BUILD}."
                    )
                shown = period
            else:
                try:
                    shown = int(self.count_var.get())
                except ValueError:
                    shown = 200
                shown = max(1, min(shown, period, MAX_PERIOD_TO_BUILD))

            init = [1] + [0] * (k - 1)
            self.progress_msg("Генерируется последовательность...")
            seq, final_state = build_sequence(F, f, init, shown)

            verified = False
            if shown == period:
                verified = (final_state == init)

            self.last_result = {
                "F": F,
                "q": q,
                "k": k,
                "f": f,
                "init": init,
                "period": period,
                "seq": seq,
                "shown": shown,
                "checked": checked,
                "total": total,
                "verified": verified,
            }

            self.root.after(0, self.redraw)
            self.root.after(0, lambda: self.status.set("Готово"))
        except InterruptedError:
            self.root.after(0, lambda: self.status.set("Прервано"))
        except Exception as e:
            self.root.after(0, lambda: messagebox.showerror("Ошибка", str(e)))
            self.root.after(0, lambda: self.status.set("Ошибка"))
        finally:
            self.root.after(0, self.finish_buttons)

    def finish_buttons(self):
        self.progress.stop()
        self.start_btn.configure(state=tk.NORMAL)
        self.stop_btn.configure(state=tk.DISABLED)

    def redraw(self):
        if not self.last_result:
            return
        r = self.last_result
        F = r["F"]
        mode = self.mode_var.get()

        lines = []
        lines.append("ГЕНЕРАТОР ЛИНЕЙНОЙ ОДНОРОДНОЙ РЕКУРРЕНТНОЙ ПОСЛЕДОВАТЕЛЬНОСТИ")
        lines.append("=" * 78)
        lines.append(F.field_explanation())
        lines.append("")
        lines.append("Параметры задачи:")
        lines.append(f"  q = {r['q']}, k = {r['k']}")
        lines.append(f"  максимальный минимальный период = q^k - 1 = {r['period']}")
        lines.append(f"  проверено кандидатов характеристического многочлена: {r['checked']} из {r['total']}")
        lines.append("")
        lines.append("Примитивный характеристический многочлен:")
        lines.append(f"  f(x) = {poly_text_field(r['f'], F)}")
        lines.append("")
        lines.append("Рекуррентное соотношение:")
        lines.append(f"  {recurrence_text(F, r['f'])}")
        lines.append("")
        lines.append("Начальный вектор состояния:")
        lines.append("  [" + ", ".join(F.element_to_text(x, mode) for x in r['init']) + "]")
        lines.append("  Используется ненулевой начальный вектор. Для примитивного многочлена любой ненулевой вектор даёт период q^k - 1.")
        lines.append("")
        lines.append(f"Последовательность, показано {r['shown']} из {r['period']} элементов. Режим вывода: {mode}.")
        lines.append("-" * 78)

        per_row = 8
        seq = r["seq"]
        for start in range(0, len(seq), per_row):
            part = seq[start:start + per_row]
            vals = [F.element_to_text(x, mode) for x in part]
            lines.append(f"s[{start:>5}] : " + " ; ".join(vals))

        if r["verified"]:
            lines.append("")
            lines.append("Период проверен: после q^k - 1 шагов состояние возвращается к начальному.")
        elif r["shown"] < r["period"]:
            lines.append("")
            lines.append(f"Остальная часть периода не выводится: ещё {r['period'] - r['shown']} элементов.")

        lines.append("")
        lines.append("Пояснение к обозначениям:")
        lines.append("  ЛОРП порядка k строится по k предыдущим элементам.")
        lines.append("  Характеристический многочлен выбран примитивным, поэтому период ненулевой последовательности максимален.")
        lines.append("  Нулевой начальный вектор не используется, потому что он даёт постоянную нулевую последовательность периода 1.")

        self.set_text("\n".join(lines))


def main():
    root = tk.Tk()
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
