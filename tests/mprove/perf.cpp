#include "mprove.h"
#include <cstdlib>
#include "../performance_tests/performance_tests.h"
#include "../performance_tests/performance_utils.h"

using namespace std;

template <size_t anonSetSize, size_t ownKeysSetSize, size_t numIterations>
class test_mprove_proof_generation
{
  public:
    static const size_t loop_count = numIterations;

    bool init()
    {
      // Third argument is a random 32 byte message
      m_exch = new MoneroExchange(anonSetSize, ownKeysSetSize);
      return true;
    }

    bool test()
    {
      MProvePlus p = m_exch->GenerateProofOfAssets();
      return true;
    }
  private:
    MoneroExchange *m_exch;
};

template <size_t anonSetSize, size_t ownKeysSetSize, size_t numIterations>
class test_mprove_proof_verification
{
  public:
    static const size_t loop_count = numIterations;

    bool init()
    {
      // Third argument is a random 32 byte message
      m_exch = new MoneroExchange(anonSetSize, ownKeysSetSize);
      m_exch->GenerateProofOfAssets();
      return true;
    }

    bool test()
    {
      return MProveProofPublicVerification(m_exch->GetProof(), m_exch->GetC_vec(), m_exch->GetP_vec(), m_exch->GetH_vec());
    }
  private:
    MoneroExchange *m_exch;
};

int main(int argc, char *argv[]) {
  set_process_affinity(1);
  set_thread_high_priority();

  Params params;
  params.verbose = true;
  params.stats = true;
  params.loop_multiplier = 1;
  string filter = "";


  performance_timer timer;
  timer.start();

  TEST_PERFORMANCE3(filter, params, test_mprove_proof_generation, 1000, 100, 10);
  TEST_PERFORMANCE3(filter, params, test_mprove_proof_generation, 1000, 500, 10);
  TEST_PERFORMANCE3(filter, params, test_mprove_proof_generation, 1000, 900, 10);

  TEST_PERFORMANCE3(filter, params, test_mprove_proof_generation, 10000, 1000, 10);
  TEST_PERFORMANCE3(filter, params, test_mprove_proof_generation, 10000, 5000, 10);
  TEST_PERFORMANCE3(filter, params, test_mprove_proof_generation, 10000, 9000, 10);

  TEST_PERFORMANCE3(filter, params, test_mprove_proof_generation, 100000, 10000, 10);
  TEST_PERFORMANCE3(filter, params, test_mprove_proof_generation, 100000, 50000, 10);
  TEST_PERFORMANCE3(filter, params, test_mprove_proof_generation, 100000, 90000, 10);

  TEST_PERFORMANCE3(filter, params, test_mprove_proof_verification, 1000, 100, 10);
  TEST_PERFORMANCE3(filter, params, test_mprove_proof_verification, 1000, 500, 10);
  TEST_PERFORMANCE3(filter, params, test_mprove_proof_verification, 1000, 900, 10);

  TEST_PERFORMANCE3(filter, params, test_mprove_proof_verification, 10000, 1000, 10);
  TEST_PERFORMANCE3(filter, params, test_mprove_proof_verification, 10000, 5000, 10);
  TEST_PERFORMANCE3(filter, params, test_mprove_proof_verification, 10000, 9000, 10);

  TEST_PERFORMANCE3(filter, params, test_mprove_proof_verification, 100000, 10000, 10);
  TEST_PERFORMANCE3(filter, params, test_mprove_proof_verification, 100000, 50000, 10);
  TEST_PERFORMANCE3(filter, params, test_mprove_proof_verification, 100000, 90000, 10);

  cout << endl <<  "Tests finished. Elapsed time: " << timer.elapsed_ms() / 1000 << " sec" << endl;
  return 0;
}
