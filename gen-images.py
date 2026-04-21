import argparse
import asyncio
import os
import subprocess
import sys
import zlib
from base64 import b64encode
from pathlib import PosixPath
from random import choice, randint

from tqdm.rich import tqdm

if sys.version_info >= (3, 14):
    from compression import zstd
else:
    from backports import zstd

CLUSTS = [512, 1024, 2048, 4096]
FS = "vfat"


async def gen(
    k,
    pbar,
    path,
    syzconv,
    genops,
    z,
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
    zpath = PosixPath(path) / f"image_{k:03}.img.zst"
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
            k,
            pbar,
            path,
            syzconv,
            genops,
            z,
            randint(0, 2**64 - 1),
            fuel1,
            fuel2,
            clust,
            blob_size,
            write_size,
        )
        return
    if syzconv:
        print(f"converting image {k}...")
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
    if z:
        print(f"compressing image {k}...")
        with open(imgpath, "rb") as img:
            with zstd.open(zpath, "wb") as zimg:
                zimg.write(img.read())
        os.remove(imgpath)
        print(f"image {k} compressed!")

    print(f"task {k} finished generating!")
    pbar.update(1)


async def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("N", type=int, help="number of images")
    parser.add_argument("path", type=str, help="images directory path")
    parser.add_argument(
        "-p", "--procs", type=int, default=os.cpu_count(), help="process count"
    )
    parser.add_argument("--syz", action="store_true", help="generate syzkaller seeds")
    parser.add_argument("--ops", action="store_true", help="generate operations")
    parser.add_argument("-z", action="store_true", help="compress images with zstd")
    args = parser.parse_args()

    os.makedirs(PosixPath(args.path), exist_ok=True)
    if args.syz:
        os.makedirs(PosixPath(args.path) / "syz", exist_ok=True)

    pbar = tqdm(total=args.N)

    task_queue = asyncio.Queue()
    for k in range(args.N):
        task_queue.put_nowait(k)

    async def worker():
        while not task_queue.empty():
            k = await task_queue.get()
            try:
                await gen(k, pbar, args.path, args.syz, args.ops, args.z)
            finally:
                task_queue.task_done()

    workers = [asyncio.create_task(worker()) for _ in range(args.procs)]
    await asyncio.gather(*workers)

    pbar.close()


if __name__ == "__main__":
    asyncio.run(main())
