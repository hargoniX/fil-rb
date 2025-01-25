from __future__ import annotations
import subprocess
import os
from dataclasses import dataclass
from typing import List, Tuple
import random
from matplotlib import pyplot as plt
import numpy as np

MIN_POW = 0
MAX_POW = 6
POINTS = 60
OUT_DIR = "plots"


@dataclass
class Result:
    random_insert: int
    random_search: int
    sequential_insert: int
    sequential_search: int

    @staticmethod
    def average(rs: List[Result]) -> Result:
        res = Result(0, 0, 0, 0)
        for r in rs:
            res.random_insert += r.random_insert
            res.random_search += r.random_search
            res.sequential_insert += r.sequential_insert
            res.sequential_search += r.sequential_search

        res.random_insert = res.random_insert // len(rs)
        res.random_search = res.random_search // len(rs)
        res.sequential_insert = res.sequential_insert // len(rs)
        res.sequential_search = res.sequential_search // len(rs)
        return res


def set_cwd():
    git_root = subprocess.check_output(
        ["git", "rev-parse", "--show-toplevel"], text=True
    ).strip()
    os.chdir(git_root)


def prepare():
    set_cwd()
    subprocess.run(["lake", "build", "Bench"])
    subprocess.run(["make", "bench"], cwd="bench-cpp")
    random.seed(37)
    os.makedirs(OUT_DIR, exist_ok=True)


def parse_out(out: str) -> Result:
    result_dict = {}

    lines = out.strip().splitlines()
    assert len(lines) == 4

    for line in lines:
        key, value = line.split()
        result_dict[key.replace("-", "_")] = int(value)

    return Result(
        random_insert=result_dict["random_insert"],
        random_search=result_dict["random_search"],
        sequential_insert=result_dict["sequential_insert"],
        sequential_search=result_dict["sequential_search"],
    )


def run_lean(seed: int, count: int) -> Result:
    out = subprocess.check_output(
        [".lake/build/bin/Bench", str(seed), str(count)], stderr=subprocess.PIPE
    ).decode()
    return parse_out(out)


def run_cpp(seed: int, count: int) -> Result:
    out = subprocess.check_output(
        ["./bench", str(seed), str(count)], stderr=subprocess.PIPE, cwd="bench-cpp"
    ).decode()
    return parse_out(out)

def counts() -> List[int]:
    return list(np.logspace(MIN_POW, MAX_POW, dtype=int, num=POINTS))


def collect_data() -> Tuple[List[Result], List[Result]]:
    lean_res = []
    cpp_res = []
    for count in counts():
        lean_try = []
        cpp_try = []
        print(f"=== Collecting data for {count} entries")
        for _ in range(5):
            seed = random.randint(1, 0x7FFFFFF0)
            lean_try.append(run_lean(seed, count))
            cpp_try.append(run_cpp(seed, count))
        lean_res.append(Result.average(lean_try))
        cpp_res.append(Result.average(cpp_try))

    return lean_res, cpp_res


def plot_data(lean_data: List[Result], cpp_data: List[Result]):
    xs = counts()

    plots = [
        "random_insert",
        "random_search",
        "sequential_insert",
        "sequential_search",
    ]

    for plot in plots:
        plt.figure()
        plt.title(f"Lean Filrb vs C++ std::map {plot}")
        plt.xlabel("Size of set")
        plt.ylabel("Time in ns")
        lean = []
        cpp = []
        for d in lean_data:
            lean.append(d.__dict__[plot])
        for d in cpp_data:
            cpp.append(d.__dict__[plot])
        plt.plot(xs, lean, label="Lean Filrb")
        plt.plot(xs, cpp, label="C++ std::map")
        plt.legend(loc="upper left")
        plt.savefig(os.path.join(OUT_DIR, f"{plot}.svg"))


def main():
    print("== Running setup")
    prepare()
    print("== Collecting data")
    lean, cpp = collect_data()
    print("== Writing output")
    plot_data(lean, cpp)


if __name__ == "__main__":
    main()
