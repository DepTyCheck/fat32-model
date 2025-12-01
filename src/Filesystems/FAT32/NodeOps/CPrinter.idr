module Filesystems.FAT32.NodeOps.CPrinter

import Filesystems.FAT32
import Filesystems.FAT32.Index
import Filesystems.FAT32.NodeOps

%default total
%hide Data.Nat.divCeilNZ
%prefix_record_projections off

header : Nat -> String
header len = #"""
#define _GNU_SOURCE

#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <errno.h>
#include <assert.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <linux/msdos_fs.h>

#define panic_on(EXPR) do {if (EXPR) {perror(""); assert(0);}} while (0)

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "Usage: ");
    fprintf(stderr, "%s", argv[0]);
    fprintf(stderr, " <mount_path>\n");
    exit(EXIT_FAILURE);
  }
  int rootfd = open(argv[1], O_PATH | O_DIRECTORY);
  panic_on(rootfd < 0);
  puts("Running \#{show len} tests...");

"""#

footer : String
footer = #"""
  int gres = close(rootfd);
  panic_on(gres < 0);
}

"""#


public export
index2UnixPath : (node : Node cfg ar wb Nameful fs) -> (idx : IndexIn node rootl dirl) -> String

index2UnixPath' : (names : UniqNames k) -> (xs : HSnocVectMaybeNode cfg k ars wb Nameful) -> (idx : IndexIn xs dirl) -> String 
index2UnixPath' (NewName y) (_ :< Just x) (Here idx) = "\{y}\{index2UnixPath x idx}"
index2UnixPath' (NewName {ff} f) (xs :< x) (There idx) = index2UnixPath' ff xs idx

index2UnixPath .(Root _ _ @{_}) HereRoot = "./"
index2UnixPath (Root {ars} (NamesSome names) xs) (ThereRoot idx) {ar=MkNodeArgs _ (_ + totsum ars)} = "./\{index2UnixPath' names xs idx}"
index2UnixPath (Dir {ars} _ (NamesSome names) xs) (ThereDir idx) {ar=MkNodeArgs _ (_ + totsum ars)} = "/\{index2UnixPath' names xs idx}"
index2UnixPath .(File _ _ @{_}) HereFile = ""
index2UnixPath .(Dir _ _ _ @{_}) HereDir = "/"
index2UnixPath .(File _ _ @{_}) (ThereDir _) impossible

bool : Bool -> String
bool True = "true"
bool False = "false"

public export
printCOps : Nat -> Nat -> {cfg : NodeCfg} -> (node : Node cfg ar Blobful Nameful Rootful) -> NodeOps cfg node -> List String
printCOps i len root (GetFlags idx cont) with (indexGet root idx)
    _ | (Evidence _ ((File meta _) ** prf)) = let path = index2UnixPath root idx in #"""
          {
            puts("Test \#{show i}/\#{show len}: GetFlags on \#{path}");
            errno = 0;
            int fd = openat(rootfd, "\#{path}", O_RDONLY);
            panic_on(fd < 0);
            uint32_t attr;
            int res = ioctl(fd, FAT_IOCTL_GET_ATTRIBUTES, &attr);
            panic_on(res < 0);
            assert(!(attr & ATTR_DIR));
            assert(\#{bool meta.readOnly} == !!(attr & ATTR_RO));
            assert(\#{bool meta.hidden} == !!(attr & ATTR_HIDDEN));
            assert(\#{bool meta.system} == !!(attr & ATTR_SYS));
            assert(\#{bool meta.archive} == !!(attr & ATTR_ARCH));
            res = close(fd);
            panic_on(res < 0);
          }

        """# :: printCOps (i + 1) len root cont
    _ | (Evidence _ ((Dir meta _ _) ** prf)) = let path = index2UnixPath root idx in #"""
          {
            puts("Test \#{show i}/\#{show len}: GetFlags on \#{path}");
            errno = 0;
            int fd = openat(rootfd, "\#{path}", O_RDONLY);
            panic_on(fd < 0);
            uint32_t attr;
            int res = ioctl(fd, FAT_IOCTL_GET_ATTRIBUTES, &attr);
            panic_on(res < 0);
            assert(attr & ATTR_DIR);
            assert(\#{bool meta.readOnly} == !!(attr & ATTR_RO));
            assert(\#{bool meta.hidden} == !!(attr & ATTR_HIDDEN));
            assert(\#{bool meta.system} == !!(attr & ATTR_SYS));
            assert(\#{bool meta.archive} == !!(attr & ATTR_ARCH));
            res = close(fd);
            panic_on(res < 0);
          }

        """# :: printCOps (i + 1) len root cont
    _ | (Evidence _ ((Root _ _) ** prf)) = let path = index2UnixPath root idx in #"""
          {
            puts("Test \#{show i}/\#{show len}: GetFlags on \#{path}");
            errno = 0;
            int fd = openat(rootfd, "\#{path}", O_RDONLY);
            panic_on(fd < 0);
            uint32_t attr;
            int res = ioctl(fd, FAT_IOCTL_GET_ATTRIBUTES, &attr);
            panic_on(res < 0);
            assert(attr & ATTR_DIR);
            assert(!(attr & ATTR_RO));
            assert(!(attr & ATTR_HIDDEN));
            assert(!(attr & ATTR_SYS));
            assert(!(attr & ATTR_ARCH));
            res = close(fd);
            panic_on(res < 0);
          }

        """# :: printCOps (i + 1) len root cont
printCOps i len root (SetFlags idx meta cont) = let path = index2UnixPath root idx in #"""
          {
            puts("Test \#{show i}/\#{show len}: SetFlags on \#{path}");
            errno = 0;
            int fd = openat(rootfd, "\#{path}", O_RDONLY);
            panic_on(fd < 0);
            uint32_t attr = 0;
            attr |= \#{if meta.readOnly then "ATTR_RO" else "0"};
            attr |= \#{if meta.hidden then "ATTR_HIDDEN" else "0"};
            attr |= \#{if meta.system then "ATTR_SYS" else "0"};
            attr |= \#{if meta.archive then "ATTR_ARCH" else "0"};
            int res = ioctl(fd, FAT_IOCTL_SET_ATTRIBUTES, &attr);
            panic_on(res < 0);
            res = close(fd);
            panic_on(res < 0);
          }

        """# :: printCOps (i + 1) len (setFlags cfg root idx meta) cont
printCOps i len root (NewDir idx name nameprf cont) = let path = index2UnixPath root idx in #"""
          {
            puts("Test \#{show i}/\#{show len}: NewDir \#{name} in \#{path}");
            errno = 0;
            int fd = openat(rootfd, "\#{path}", O_PATH | O_DIRECTORY);
            panic_on(fd < 0);
            int res = mkdirat(fd, "\#{name}", 0777);
            panic_on(res < 0);
            res = close(fd);
            panic_on(res < 0);
          }

        """# :: printCOps (i + 1) len (snd $ newDir cfg root idx name nameprf) cont
printCOps i len root (NewFile idx name nameprf cont) = let path = index2UnixPath root idx in #"""
          {
            puts("Test \#{show i}/\#{show len}: NewFile \#{name} in \#{path}");
            errno = 0;
            int fd = openat(rootfd, "\#{path}", O_PATH | O_DIRECTORY);
            panic_on(fd < 0);
            int res = openat(rootfd, "\#{name}", O_CREAT | O_EXCL | O_WRONLY);
            panic_on(res < 0);
            res = close(fd);
            panic_on(res < 0);
          }

        """# :: printCOps (i + 1) len (snd $ newFile cfg root idx name nameprf) cont
printCOps _ _ _ Nop = [#"puts("All done!");\#n"#]

public export
buildCProg : (cfg : NodeCfg) -> (root : Node cfg ar Blobful Nameful Rootful) -> (ops : NodeOps cfg root) -> String
buildCProg cfg root ops = let len = length ops in header len ++ concat (printCOps 1 len root ops) ++ footer
