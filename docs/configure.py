import glob


def createNinja(f):
    f.write("rule alectryon\n")
    f.write("  command = alectryon --frontend lean4+markup $in --backend webpage --lake lakefile.lean -o $out\n")
    f.write("rule book\n")
    f.write("  command = mdbook build\n")

    all_files = []
    for d in [".", "Basics", "BackwardProofs", "ForwardProofs", "FunctionalProgramming"]:
        for path in glob.glob(f"{d}/*.lean"):
            n = path.replace('\\', '/')
            if "lakefile.lean" not in n:
                f.write(f"build {n}.md: alectryon {n}\n")
                all_files += [n+".md"]

    f.write("build docs/index.html: book " + " ".join(all_files) + "\n")


if __name__ == '__main__':
    with open("build.ninja", 'w') as f:
        createNinja(f)
