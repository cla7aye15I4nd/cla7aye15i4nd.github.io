from __future__ import annotations

import base64
from io import BytesIO
from pathlib import Path

import numpy as np
from PIL import Image

ROOT = Path(__file__).resolve().parents[1]
REFERENCE = Path("/Users/moe/Downloads/IMG_1759.jpg")
OUTPUT = ROOT / "templates" / "partials" / "dumpling_svg.html"
PADDING = 18


def content_bbox(pixels: np.ndarray) -> tuple[int, int, int, int]:
    # Treat the almost-white screenshot background as empty space.
    mask = np.any(pixels[:, :, :3] < 245, axis=2)
    ys, xs = np.where(mask)
    return int(xs.min()), int(ys.min()), int(xs.max()), int(ys.max())


def crop_to_sticker(image: Image.Image) -> Image.Image:
    rgba = image.convert("RGBA")
    pixels = np.asarray(rgba)
    left, top, right, bottom = content_bbox(pixels)
    left = max(0, left - PADDING)
    top = max(0, top - PADDING)
    right = min(image.width - 1, right + PADDING)
    bottom = min(image.height - 1, bottom + PADDING)
    cropped = rgba.crop((left, top, right + 1, bottom + 1))

    data = np.asarray(cropped).copy()
    rgb = data[:, :, :3].astype(np.int16)
    distance_from_white = 255 - rgb.min(axis=2)

    alpha = data[:, :, 3].astype(np.float32)
    alpha[distance_from_white <= 5] = 0
    soft = (distance_from_white > 5) & (distance_from_white < 28)
    alpha[soft] *= (distance_from_white[soft] - 5) / 23
    data[:, :, 3] = np.clip(alpha, 0, 255).astype(np.uint8)
    return Image.fromarray(data, "RGBA")


def png_data_url(image: Image.Image) -> str:
    buffer = BytesIO()
    image.save(buffer, format="PNG", optimize=True)
    encoded = base64.b64encode(buffer.getvalue()).decode("ascii")
    return f"data:image/png;base64,{encoded}"


def main() -> None:
    sticker = crop_to_sticker(Image.open(REFERENCE))
    width, height = sticker.size
    data_url = png_data_url(sticker)

    html = f"""<svg class="not-found-dumpling" viewBox="0 0 {width} {height}" role="img" aria-label="A rotating dumpling">
  <g class="dumpling-spin">
    <image class="dumpling-reference" href="{data_url}" width="{width}" height="{height}" decoding="async"/>
  </g>
</svg>
"""
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(html, encoding="utf-8")
    print(f"wrote {OUTPUT.relative_to(ROOT)} from {REFERENCE} ({width}x{height})")


if __name__ == "__main__":
    main()
