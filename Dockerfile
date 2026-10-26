# One-command replication of the VWZ formalization.
#
# The image is deliberately thin. The official Isabelle image already contains the
# distribution, the JDK and the system libraries it needs, so there is nothing to
# download here. Hand-rolling it from a tarball would add ~3 GB to the image and one
# more version string to get wrong (the release is `Isabelle2025-2`, not `Isabelle2025`).
#
#   docker build -t vwz .
#   docker run --rm -v "$PWD:/workspace" -w /workspace vwz build -b -c -D aligned
#
# The entry point is spelled out as an absolute path on purpose. The base image declares
#   Entrypoint: ["Isabelle/bin/isabelle"]   WorkingDir: /home/isabelle
# i.e. a *relative* path that resolves against its own working directory. Inheriting it
# while changing the working directory gives "exec: Isabelle/bin/isabelle: no such file
# or directory", and plain `ENTRYPOINT ["isabelle"]` fails too, because an exec-form
# entry point is not looked up in the image's PATH (isabelle is not on it).
#
# The RUN line below is the guard: if the base image ever moves the distribution, the
# image stops building, loudly, instead of failing at run time with a confusing error.
FROM makarius/isabelle:Isabelle2025-2

RUN /home/isabelle/Isabelle/bin/isabelle version

ENTRYPOINT ["/home/isabelle/Isabelle/bin/isabelle"]

WORKDIR /workspace
COPY . /workspace
