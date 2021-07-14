This directory has two scripts which were used to measure the time taken to check whether some key images have appeared on the blockchain.

  - `keyimage_file_generator.py`

      Running `python keyimage_file_generator.py <anon_set_size> <image_file>` will create a file called `image_file` containing `anon_set_size` random key images (essentially random 64-digit hex strings).

      For example, `python keyimage_file_generator.py 1000 images.json`.



  - `spent_status_checker.py`

    Running `python spent_status_checker.py <image_file>` will do the following:

      + Load all the key images from `image_file`
      + Do a batch query on `http://127.0.0.1:18081/is_key_image_spent`
      + Check if all the key images are unspent.

    For example, `python spent_status_checker.py image.json`.

The running time of the `spent_status_checker.py` script depends on how much of the key image data (stored in an LMDB instance) is available in RAM. The below table shows the running times and memory consumption resulting from a sequence of consecutive runs of the following command:

```
python keyimage_file_generator.py 100000 images.json && time python spent_status_checker.py images.json
```
The running times in the last column are in seconds. The VIRT and RES columns represent the virtual memory and RAM used by the `monerod` process in GiB units after each run. The run number 0 row corresponds to the memory consumption before the first run of the above command. These results were generated in April 2019 on a Dell Optiplex 7050 desktop with a 3.6 GHz i7 CPU, 8GB RAM, and 1 TB HDD. During this measurement, the block height of the Monero blockchain was between 1817834 and 1817858.

| Run No. | VIRT (GiB)  | RES (GiB)  | Run Time (secs)   |
| ------: | ----------: | ---------: | ----------------: |
| 0       | 78.254      | 0.333      | NA                |
| 1       | 78.254      | 0.796      | 646.488           |
| 2       | 78.317      | 1.029      | 459.498           |
| 3       | 78.317      | 1.192      | 332.723           |
| 4       | 78.317      | 1.308      | 242.530           |
| 5       | 78.598      | 1.393      | 177.068           |
| 6       | 78.598      | 1.453      | 129.263           |
| 7       | 78.598      | 1.497      | 95.619            |
| 8       | 78.598      | 1.529      | 70.324            |
| 9       | 78.598      | 1.553      | 51.862            |
| 10      | 78.598      | 1.571      | 39.564            |
| 11      | 78.598      | 1.584      | 29.012            |
| 12      | 78.598      | 1.594      | 21.767            |
| 13      | 78.598      | 1.602      | 17.643            |
| 14      | 78.598      | 1.607      | 12.969            |
| 15      | 78.598      | 1.611      | 10.537            |
| 16      | 78.598      | 1.615      | 8.454             |
| 17      | 78.598      | 1.618      | 6.818             |
| 18      | 78.598      | 1.619      | 5.287             |
| 19      | 78.598      | 1.621      | 4.099             |
| 20      | 78.598      | 1.624      | 3.590             |
| 21      | 78.598      | 1.624      | 2.807             |
| 22      | 78.598      | 1.625      | 2.758             |
| 23      | 78.598      | 1.626      | 1.958             |
| 24      | 78.598      | 1.626      | 1.992             |
| 25      | 78.598      | 1.627      | 1.245             |
| 26      | 78.598      | 1.627      | 1.345             |
| 27      | 78.598      | 1.627      | 0.989             |
| 28      | 78.598      | 1.628      | 0.939             |
| 29      | 78.598      | 1.628      | 0.822             |
| 30      | 78.598      | 1.628      | 0.696             |
| 31      | 78.598      | 1.628      | 0.541             |
| 32      | 78.598      | 1.628      | 0.565             |
| 33      | 78.598      | 1.628      | 0.536             |
| 34      | 78.598      | 1.628      | 0.537             |
| 35      | 78.598      | 1.628      | 0.743             |
| 36      | 78.598      | 1.628      | 0.529             |
| 37      | 78.598      | 1.628      | 0.693             |
| 38      | 78.598      | 1.628      | 0.526             |
| 39      | 78.598      | 1.628      | 0.697             |
| 40      | 78.598      | 1.628      | 0.647             |
| 41      | 78.598      | 1.628      | 0.517             |
| 42      | 78.598      | 1.628      | 0.509             |
| 43      | 78.598      | 1.628      | 0.515             |
| 44      | 78.598      | 1.629      | 0.520             |
| 45      | 78.598      | 1.629      | 0.490             |
| 46      | 78.598      | 1.629      | 0.493             |
| 47      | 78.598      | 1.629      | 0.487             |
| 48      | 78.598      | 1.629      | 0.513             |
| 49      | 78.598      | 1.629      | 0.495             |
| 50      | 78.598      | 1.629      | 0.494             |
| 51      | 78.598      | 1.629      | 0.477             |

