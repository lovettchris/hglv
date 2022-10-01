import os
import glob
import ninja_syntax

script_path = os.path.dirname(__file__)

def createNinja(f):
    ninja = ninja_syntax.Writer(f)
    ninja.rule(name="alectryon", command="alectryon --frontend lean4+markup $in --lake lakefile.lean --backend webpage -o $out")
    ninja.rule(name="book", command="mdbook build")

    os.chdir(script_path)
    all_files = []
    for d in os.listdir(script_path):
        if os.path.isdir(d) and d != "__pycache__" and d != "build" and d != "lean_packages" and d != ".git" and d != "docs":
            print(f"collecting .lean source files in {d}")
            for path in glob.glob(f"{d}/*.lean"):
                n = path.replace('\\', '/')
                if "lakefile.lean" not in n:
                    ninja.build(outputs=f"{n}.md", rule="alectryon", inputs=f"{n}")
                    all_files += [f"{n}.md"]

    print("collecting all md files...")
    for path in glob.glob("**/*.md", recursive=True):
        if not path.startswith("ninja"):
            n = path.replace('\\', '/')
            if n not in all_files:
                all_files += [n]

    ninja.build(outputs="docs/index.html", rule="book", inputs=all_files)


if __name__ == '__main__':
    with open("build.ninja", 'w') as f:
        createNinja(f)

    print ("Now you can run 'ninja' to build the docs then you can open ./docs/index.html in your browser.")
