import os
import json
import argparse

parser= argparse.ArgumentParser()
parser.add_argument("anon_set_size", help="Size of anonymity set", type=int)
parser.add_argument("image_file_name", help="Name of file having list of key images", type=str)
args = parser.parse_args()
headers = { 'Content-Type': 'application/json', }
num_digits=64

image_list = [str(os.urandom(num_digits / 2).encode('hex')) for i in range(args.anon_set_size)]
data_dict = {'key_images' : image_list}
data_json = json.dumps(data_dict)

with open(args.image_file_name, 'w') as images_file:
    json.dump(data_json, images_file)
