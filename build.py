#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""把 src/ 与 assets/ 拼装成单文件 HTML，并做基本自检。"""
import io
import os
import re
import subprocess
import sys
import tempfile

BASE = os.path.dirname(os.path.abspath(__file__))


def read(rel):
    with io.open(os.path.join(BASE, rel), "r", encoding="utf-8") as f:
        return f.read()


def write(rel, text):
    with io.open(os.path.join(BASE, rel), "w", encoding="utf-8") as f:
        f.write(text)


def main():
    tpl = read("src/template.html")
    css = read("src/style.css")
    three = read("assets/three.min.js")
    game = read("src/game.js")

    # 1) 注入前必须断言没有提前闭合标签
    for name, val in (("css", css), ("three", three), ("game", game)):
        assert "</script" not in val.lower(), "bad script tag in " + name
        assert "</style" not in val.lower(), "bad style tag in " + name

    out = tpl.replace("__CSS__", css).replace("__THREE__", three).replace("__GAME__", game)

    # 2) 标签配对自检
    for tag in ("script", "style", "div", "svg", "button"):
        o = len(re.findall(r"<" + tag + r"[\s>]", out))
        c = len(re.findall(r"</" + tag + r">", out))
        assert o == c, "tag mismatch <%s>: open=%d close=%d" % (tag, o, c)

    # 3) 不允许外部依赖（w3.org 命名空间常量不算）
    for pat in ('src="http', "src='http", 'href="http', "href='http",
                "url(http", "@import", "//unpkg", "//cdn"):
        assert pat not in out, "external ref found: " + pat

    # 4) JS 语法检查（写系统临时目录，绝不落进仓库）
    fd, tmp = tempfile.mkstemp(suffix=".js", prefix="snake_check_")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(game)
        r = subprocess.run(["node", "--check", tmp], capture_output=True, text=True)
        if r.returncode != 0:
            sys.stderr.write(r.stderr)
            raise SystemExit("game.js 语法错误")
    finally:
        try:
            os.remove(tmp)
        except OSError:
            pass

    out_path = os.path.join(BASE, "index.html")
    write("index.html", out)

    size = os.path.getsize(out_path)
    print("OK  -> index.html  %.1f KB  (css %d / three %d / game %d bytes)"
          % (size / 1024.0, len(css), len(three), len(game)))


if __name__ == "__main__":
    main()
