import asyncio
import os
import subprocess
import sys
import zlib
from base64 import b64encode
from pathlib import PosixPath
from random import choice, randint

CLUSTS = [512, 1024, 2048, 4096]


async def gen(k, path, seed=None, fuel1=None, fuel2=None, clust=None):
    if seed is None:
        seed = randint(0, 2**64 - 1)
    if fuel1 is None:
        fuel1 = randint(12, 20)
    if fuel2 is None:
        fuel2 = 2 * fuel1
    if clust is None:
        clust = choice(CLUSTS)

    imgpath = PosixPath(path) / f"image_{k:03}.img"
    syzpath = PosixPath(path) / "syz" / f"syz_mount_image_msdos_idris_{k:03}"

    print(
        f"generating #{k} (seed={seed}, fuel1={fuel1}, fuel2={fuel2}, clsize={clust})..."
    )
    proc = await asyncio.create_subprocess_exec(
        "unbuffer",
        "pack",
        "run",
        "fat32-model",
        "-s",
        str(seed),
        "-1",
        str(fuel1),
        "-2",
        str(fuel2),
        "-c",
        str(clust),
        "-o",
        str(imgpath),
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    while line := await proc.stdout.readline():
        print(f"[#{k:03}] {line.decode()}", end='')
    await proc.wait()
    if proc.returncode != 0:
        print(f"task #{k} failed with exit code {proc.returncode}")
        return
    print(f"task {k} finished generating, converting...")
    with open(imgpath, "rb") as img:
        data = img.read()
    cvt = b64encode(zlib.compress(data)).decode()
    with open(syzpath, "w") as syz:
        syz.write(
            f"# image_{k:03}, seed={seed}, fuel1={fuel1}, fuel2={fuel2}, clsize={clust}\n\n"
        )
        syz.write(
            f"syz_mount_image$msdos(&AUTO='msdos\\x00', &AUTO='./file0\\x00', 0x0, &AUTO, 0x1, AUTO, &AUTO=\""
        )
        syz.write(cvt)
        syz.write('")\n')
    print(f"image {k} converted!")


async def main():
    _, N, path = sys.argv
    N = int(N)
    os.makedirs(PosixPath(path) / "syz", exist_ok=True)
    await asyncio.gather(*(gen(k, path) for k in range(N)))


if __name__ == "__main__":
    asyncio.run(main())
