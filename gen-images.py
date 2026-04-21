import argparse
import asyncio
import os
import subprocess
import zlib
from base64 import b64encode
from pathlib import PosixPath
from random import choice, randint

CLUSTS = [512, 1024, 2048, 4096]
FS = "vfat"


async def gen(
    k,
    path,
    syzconv,
    genops,
    seed=None,
    fuel1=None,
    fuel2=None,
    clust=None,
    blob_size=None,
    write_size=None,
):
    if seed is None:
        seed = randint(0, 2**64 - 1)
    if fuel1 is None:
        fuel1 = randint(20, 28)
    if fuel2 is None:
        fuel2 = randint(100, 300)
    if clust is None:
        clust = choice(CLUSTS)
    if blob_size is None:
        blob_size = randint(1024, 2048)
    if write_size is None:
        write_size = randint(128, 256)

    outpath = PosixPath(path) / f"image_{k:03}"
    imgpath = PosixPath(path) / f"image_{k:03}.img"
    syzpath = PosixPath(path) / "syz" / f"syz_mount_image_{FS}_idris_{k:03}"

    print(
        f"generating #{k} (seed={seed}, fuel1={fuel1}, fuel2={fuel2}, clsize={clust}, blob_size={blob_size}, write_size={write_size})..."
    )
    proc = await asyncio.create_subprocess_exec(
        "unbuffer",
        "build/exec/fat32-model",
        "-s",
        str(seed),
        "-1",
        str(fuel1),
        "-2",
        str(fuel2),
        "-c",
        str(clust),
        "-b",
        str(blob_size),
        "-w",
        str(write_size),
        "-o",
        str(outpath),
        *([] if genops else ["--image-only"]),
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    while line := await proc.stdout.readline():
        print(f"[#{k:03}] {line.decode()}", end="")
    await proc.wait()
    if proc.returncode != 0:
        print(f"task #{k} failed with exit code {proc.returncode}, retrying...")
        await gen(
            k, path, syzconv, genops, randint(0, 2**64 - 1), fuel1, fuel2, clust, blob_size, write_size
        )
        return
    if syzconv:
        print(f"task {k} finished generating, converting...")
        with open(imgpath, "rb") as img:
            data = img.read()
        cvt = b64encode(zlib.compress(data)).decode()
        with open(syzpath, "w") as syz:
            syz.write(
                f"# image_{k:03}, seed={seed}, fuel1={fuel1}, fuel2={fuel2}, clsize={clust}\n\n"
            )
            syz.write(
                f"syz_mount_image${FS}(&AUTO='{FS}\\x00', &AUTO='./file0\\x00', 0x0, &AUTO, 0x1, AUTO, &AUTO=\"$"
            )
            syz.write(cvt)
            syz.write('")\n')
        print(f"image {k} converted!")
    else:
        print(f"task {k} finished generating!")


async def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("N", type=int, help="number of images")
    parser.add_argument("path", type=str, help="images directory path")
    parser.add_argument(
        "-p", "--procs", type=int, default=os.cpu_count(), help="process count"
    )
    parser.add_argument("--syz", action="store_true", help="generate syzkaller seeds")
    parser.add_argument("--ops", action="store_true", help="generate operations")
    args = parser.parse_args()

    os.makedirs(PosixPath(args.path), exist_ok=True)
    if args.syz:
        os.makedirs(PosixPath(args.path) / "syz", exist_ok=True)
    tasks = (gen(k, args.path, args.syz, args.ops) for k in range(args.N))

    async def worker():
        for task in tasks:
            await task

    await asyncio.gather(*[worker() for i in range(args.procs)])  # type: ignore


if __name__ == "__main__":
    asyncio.run(main())
