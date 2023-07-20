
import json
import os

# Read propProblems.json file
with open('app/propProblems.json') as file:
    probs = json.load(file)


def collect_sentences(json_data):
    sentences = []
    for entry in json_data:
        for key, value in entry["soa"].items():
            sentences.append(value)
    return sentences


# get em
sentences_list = collect_sentences(probs)
print(sentences_list)


# Get the directory path of the current script
script_directory = os.path.dirname(os.path.abspath(__file__))

# Specify the output file path in the same directory
output_file_path = os.path.join(script_directory, 'sentences.json')

# Write the modified entries to the JSON file
with open(output_file_path, 'w') as file:
    json.dump(sentences_list, file, ensure_ascii=False)
