import re
import json
import os

# Read the JSON file
with open('oldProblems.json') as file:
    my_entries = json.load(file)


def convert_entries(entries):
    modified_entries = []

    for i, entry in enumerate(entries):
        modified_entry = {}

        # Assigning 'id'
        modified_entry["id"] = i + 1

        # Extracting 'sentence'
        modified_entry["sentence"] = entry["textToSymbolise"]

        # Extracting 'soa'
        soa = {}
        for item in entry["checkConfig"]["soa"]:
            soa[item["l"]] = item["t"]
        modified_entry["soa"] = soa

        # Extracting 'form'
        form = entry["checkConfig"]["sentences"][0]
        form = re.sub(r'\?', '∃', form)
        form = re.sub(r'!', '∀', form)
        form = re.sub(r'~', '¬', form)
        form = re.sub(r' /\\ ', '∧', form)
        form = re.sub(r' \\/ ', '∨', form)
        form = re.sub(r' <-> ', '↔', form)
        form = re.sub(r' -> ', '→', form)
        form = re.sub(r'\s', '', form)
        modified_entry["form"] = form
        modified_entries.append(modified_entry)

    return modified_entries


# Convert the entries
modified_entries = convert_entries(my_entries)

for entry in modified_entries:
    print(entry)

# Get the directory path of the current script
script_directory = os.path.dirname(os.path.abspath(__file__))

# Specify the output file path in the same directory
output_file_path = os.path.join(script_directory, 'modified_entries.json')

# Write the modified entries to the JSON file
with open(output_file_path, 'w') as file:
    json.dump(modified_entries, file, ensure_ascii=False)
