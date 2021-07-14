import json
import requests
import argparse

parser = argparse.ArgumentParser()
parser.add_argument("image_file_name", help="Name of file having list of key images", type=str)
args = parser.parse_args()

with open(args.image_file_name) as f:
      data = json.load(f)

headers = { 'Content-Type': 'application/json', }

response = requests.post('http://127.0.0.1:18081/is_key_image_spent', headers=headers, data=data)
print(response)
#print(response.text)
rjson = response.json()
spent_status_list = rjson['spent_status']
all_unspent = all(x==0 for x in spent_status_list)
if all_unspent:
    print("All key images are unspent")
else:
    print("Some key images are spent")

