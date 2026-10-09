/* Tiny trusted helper executed by Lean during Comparator's solution build.
 * Its location under the trusted Lean prefix uses Comparator's existing execute
 * permission; no extra Landrun permissions or wrapper are introduced.
 * Returns errno for real operations, rather than treating every error as denial.
 */
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <sys/socket.h>
#include <unistd.h>

static int append_probe(const char *path) {
    int fd = open(path, O_WRONLY | O_APPEND);
    if (fd < 0) return errno;
    ssize_t written = write(fd, "\n", 1);
    int result = written == 1 ? 0 : (written < 0 ? errno : EIO);
    if (close(fd) != 0 && result == 0) result = errno;
    return result;
}

static int socket_probe(int type) {
    int fd = socket(AF_UNIX, type, 0);
    if (fd < 0) return errno;
    return close(fd) == 0 ? 0 : errno;
}

int main(int argc, char **argv) {
    const char *labels[] = {"allowed", "challenge", "config", "tool", "outside", "symlink"};
    if (argc != 7) {
        fputs("expected six probe file paths\n", stderr);
        return 2;
    }
    putchar('{');
    for (int i = 0; i < 6; ++i)
        printf("\"%s\":%d,", labels[i], append_probe(argv[i + 1]));
    printf("\"unix_stream\":%d,\"unix_dgram\":%d}\n",
           socket_probe(SOCK_STREAM), socket_probe(SOCK_DGRAM));
    return ferror(stdout) ? 3 : 0;
}
