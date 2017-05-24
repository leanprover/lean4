import json
import os
import requests
import subprocess

def get_packages():
    script_path = os.path.dirname(os.path.realpath(__file__))
    pkg_registry = os.path.join(script_path, "package_registry.json")
    pkg_json = json.loads(open(pkg_registry, 'r').read())
    return pkg_json['packages']

def get_package_name(pkg):
    return pkg.split("/")[-1]

def clone_package(pkg):
    subprocess.run(["git", "clone", pkg])

def git_pull():
    subprocess.run(["git", "pull"])

def leanpkg_test():
    proc = subprocess.run(["leanpkg", "test"])
    if proc.returncode == 0:
        return True
    else:
        return False

def test_package(cache_dir, pkg):
    pkg_name = get_package_name(pkg)
    pkg_dir = os.path.join(cache_dir, pkg_name)

    working_dir = os.getcwd()

    if os.path.exists(pkg_dir):
        os.chdir(pkg_dir)
        git_pull()
    else:
        os.chdir(cache_dir)
        clone_package(pkg)
        os.chdir(pkg_name)

    succeded = leanpkg_test()
    os.chdir(working_dir)
    return succeded

def main():
    pkgs = get_packages()

    if not os.path.exists("packages"):
        os.makedirs("packages")

    for pkg in pkgs:
        if not test_package("packages", pkg):
            exit(-1)

    exit(0)


if __name__ == "__main__":
    main()


