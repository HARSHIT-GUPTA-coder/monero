#include "mprove.h"
#include <cstdlib>

using namespace std;

int main(int argc, char *argv[]) {
  if (argc < 4)
  {
    cout << "Usage: mprove-tests anonSetSize ownKeysSetSize print" << endl;
    cout << "print should be 0 or 1" << endl;
    return 1;
  }
  int anonSetSize, ownKeysSetSize, print;
  anonSetSize = atoi(argv[1]);
  ownKeysSetSize = atoi(argv[2]);
  print = atoi(argv[3]);

  MoneroExchange exch(anonSetSize, ownKeysSetSize);
  cout<<"exchange creation successful"<<endl;
  MProvePlus p = exch.GenerateProofOfAssets();
  cout<<"proof generation successful"<<endl;
  MProveProofPublicVerification(p, exch.GetC_vec(), exch.GetP_vec(), exch.GetH_vec());
  // exch.PrivatelyVerifyProofOfAssets();
  cout << "Proof size = " << exch.ProofSize() << endl;
  cout << "Proof size = " << sizeof(p) << endl;

  if(print)
  {
    exch.PrintExchangeState();
  }
  return 0;
}
