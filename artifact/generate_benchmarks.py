from pathlib import Path

input_directory = "TODO" # path to benchmark set
output_directory = "TODO" # path to new benchmark set

diff_file = "qfnra.diff" # "qfnra_hard.diff"

with open(diff_file, "r") as f:
    lines = f.readlines()

for l in lines:
    filename, diff = l.split(" ", 1)

    with open(input_directory + "/" + filename, "r") as f:
        input_lines = f.readlines()

    # OptiMathSat does not work with variables named pi or hashtags
    contains_pi = False
    contains_hash = False

    for i in range(len(input_lines)):
        if "declare-fun" in input_lines[i] or "declare-const" in input_lines[i]:
            var = input_lines[i].split(" ")[1]
            if var == "pi":
                contains_pi = True
            elif "#" in var:
                contains_hash = True

    if not (contains_pi or contains_hash):
        continue

    symbol = "_"

    def contains_replacement(s):
        return (
            (contains_pi and any([(s + "pi" + s) in l for l in input_lines]))
            or
            (contains_hash and any([(s + "hash" + s) in l for l in input_lines]))
        )

    while contains_replacement(symbol):
        symbol += "_"

    for i in range(len(input_lines)):
        if contains_pi:
            input_lines[i] = input_lines[i].replace("pi", symbol + "pi" + symbol)
        if contains_hash:
            input_lines[i] = input_lines[i].replace("#", symbol + "hash" + symbol)
        if "(check-sat)" in input_lines[i]:
            # add objective at the right place
            input_lines[i] = input_lines[i].replace("(check-sat)", diff+"(check-sat)")

    # make sure the file and path exist
    new_file = output_directory + "/" + filename
    Path(new_file).parents[0].mkdir(parents=True, exist_ok=True)

    with open(new_file, "w") as f:
        f.writelines(input_lines)