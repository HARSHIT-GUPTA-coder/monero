#include <stdlib.h>
#include <openssl/ssl.h>
#include <openssl/bn.h>
#include <boost/thread/mutex.hpp>
#include <boost/thread/lock_guard.hpp>
#include "ringct/rctOps.h"
#include "ringct/multiexp.h"
#include "ringct/rctSigs.h"
#include "ringct/rctTypes.h"
#include "cryptonote_basic/cryptonote_basic.h"
#include "../io.h"
#include <algorithm>

#define STRAUS_SIZE_LIMIT 232
#define PIPPENGER_SIZE_LIMIT 0

std::ostream& operator <<(std::ostream& c,rct::key &v){
  for(auto &i: v.bytes) c<<int(i)<<' ';
	return c;
}

static constexpr size_t maxProofSize = 1e6;

static rct::keyV Hi, Gi;
static std::vector<ge_p3> Hi_p3, Gi_p3;
static rct::key F;
static ge_p3 F_p3;
static std::shared_ptr<rct::straus_cached_data> straus_HiGi_cache;
static std::shared_ptr<rct::pippenger_cached_data> pippenger_HiGi_cache;
static const rct::key TWO = { {0x02, 0x00, 0x00,0x00 , 0x00, 0x00, 0x00,0x00 , 0x00, 0x00, 0x00,0x00 , 0x00, 0x00, 0x00,0x00 , 0x00, 0x00, 0x00,0x00 , 0x00, 0x00, 0x00,0x00 , 0x00, 0x00, 0x00,0x00 , 0x00, 0x00, 0x00,0x00  } };
static const rct::key MINUS_ONE = { { 0xec, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10 } };
static const rct::key MINUS_INV_EIGHT = { { 0x74, 0xa4, 0x19, 0x7a, 0xf0, 0x7d, 0x0b, 0xf7, 0x05, 0xc2, 0xda, 0x25, 0x2b, 0x5c, 0x0b, 0x0d, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0a } };
static boost::mutex init_mutex;

static inline rct::key multiexp(const std::vector<rct::MultiexpData> &data, size_t HiGi_size)
{
  if (HiGi_size > 0)
  {
    static_assert(232 <= STRAUS_SIZE_LIMIT, "Straus in precalc mode can only be calculated till STRAUS_SIZE_LIMIT");
    return HiGi_size <= 232 && data.size() == HiGi_size ? rct::straus(data, straus_HiGi_cache, 0) : rct::pippenger(data, pippenger_HiGi_cache, HiGi_size, rct::get_pippenger_c(data.size()));
  }
  else
    return data.size() <= 95 ? rct::straus(data, NULL, 0) : rct::pippenger(data, NULL, 0, rct::get_pippenger_c(data.size()));
}

static inline bool is_reduced(const rct::key &scalar)
{
  return sc_check(scalar.bytes) == 0;
}


static rct::key get_exponent(const rct::key &base, size_t idx)
{
  static const std::string domain_separator(config::HASH_KEY_BULLETPROOF_EXPONENT);
  std::string hashed = std::string((const char*)base.bytes, sizeof(base)) + domain_separator + tools::get_varint_data(idx);
  rct::key e;
  ge_p3 e_p3;
  rct::hash_to_p3(e_p3, rct::hash2rct(crypto::cn_fast_hash(hashed.data(), hashed.size())));
  ge_p3_tobytes(e.bytes, &e_p3);
  CHECK_AND_ASSERT_THROW_MES(!(e == rct::identity()), "Exponent is point at infinity");
  return e;
}

static void init_exponents(size_t ProofSize)
{
  boost::lock_guard<boost::mutex> lock(init_mutex);

  static bool init_done = false;
  if (init_done)
    return;
  std::vector<rct::MultiexpData> data;
  data.reserve(2*ProofSize + 1);
  Hi.resize(ProofSize);
  Gi.resize(ProofSize);
  Hi_p3.resize(ProofSize);
  Gi_p3.resize(ProofSize);
  size_t i;
  for ( i = 0; i < ProofSize; ++i)
  {
    Hi[i] = get_exponent(rct::H, i * 2);
    CHECK_AND_ASSERT_THROW_MES(ge_frombytes_vartime(&Hi_p3[i], Hi[i].bytes) == 0, "ge_frombytes_vartime failed");
    Gi[i] = get_exponent(rct::H, i * 2 + 1);
    CHECK_AND_ASSERT_THROW_MES(ge_frombytes_vartime(&Gi_p3[i], Gi[i].bytes) == 0, "ge_frombytes_vartime failed");

    data.push_back({rct::zero(), Gi[i]});
    data.push_back({rct::zero(), Hi[i]});

  }

  F = get_exponent(rct::H, i*2);
  CHECK_AND_ASSERT_THROW_MES(ge_frombytes_vartime(&F_p3, F.bytes) == 0, "ge_frombytes_vartime failed");

  data.push_back({rct::zero(), F});
  straus_HiGi_cache = rct::straus_init_cache(data, 0);
  pippenger_HiGi_cache = rct::pippenger_init_cache(data, 0, PIPPENGER_SIZE_LIMIT);
  init_done = true;
}

/* Compute a custom vector-scalar commitment */
static rct::key cross_vector_exponent(size_t size, const std::vector<ge_p3> &A, size_t Ao, const std::vector<ge_p3> &B, size_t Bo, const rct::keyV &a, size_t ao, const rct::keyV &b, size_t bo, const rct::keyV *scale, const ge_p3 *extra_point, const rct::key *extra_scalar)
{
  CHECK_AND_ASSERT_THROW_MES(size + Ao <= A.size(), "Incompatible size for A");
  CHECK_AND_ASSERT_THROW_MES(size + Bo <= B.size(), "Incompatible size for B");
  CHECK_AND_ASSERT_THROW_MES(size + ao <= a.size(), "Incompatible size for a");
  CHECK_AND_ASSERT_THROW_MES(size + bo <= b.size(), "Incompatible size for b");
  CHECK_AND_ASSERT_THROW_MES(!scale || size == scale->size() / 2, "Incompatible size for scale");

  std::vector<rct::MultiexpData> multiexp_data;
  multiexp_data.resize(size*2 + (!!extra_point));
  for (size_t i = 0; i < size; ++i)
  {
    multiexp_data[i*2].scalar = a[ao+i];
    multiexp_data[i*2].point = A[Ao+i];
    multiexp_data[i*2+1].scalar = b[bo+i];
    if (scale)
      sc_mul(multiexp_data[i*2+1].scalar.bytes, multiexp_data[i*2+1].scalar.bytes, (*scale)[Bo+i].bytes);
    multiexp_data[i*2+1].point = B[Bo+i];
  }
  if (extra_point)
  {
    multiexp_data.back().scalar = *extra_scalar;
    multiexp_data.back().point = *extra_point;
  }
  return multiexp(multiexp_data, 0);
}
/* Given a scalar, construct a vector of powers */
static rct::keyV vector_powers(const rct::key &x, size_t n)
{
  rct::keyV res(n);
  if (n == 0)
    return res;
  res[0] = rct::identity();
  if (n == 1)
    return res;
  res[1] = x;
  for (size_t i = 2; i < n; ++i)
  {
    sc_mul(res[i].bytes, res[i-1].bytes, x.bytes);
  }
  return res;
}

/* Given two scalar arrays, construct the inner product */
static rct::key inner_product(const epee::span<const rct::key> &a, const epee::span<const rct::key> &b)
{
  CHECK_AND_ASSERT_THROW_MES(a.size() == b.size(), "Incompatible sizes of a and b");
  rct::key res = rct::zero();
  for (size_t i = 0; i < a.size(); ++i)
  {
    sc_muladd(res.bytes, a[i].bytes, b[i].bytes, res.bytes);
  }
  return res;
}

static rct::key inner_product(const rct::keyV &a, const rct::keyV &b)
{
  return inner_product(epee::span<const rct::key>(a.data(), a.size()), epee::span<const rct::key>(b.data(), b.size()));
}

/* Given two scalar arrays, construct the Hadamard product */
static rct::keyV hadamard(const rct::keyV &a, const rct::keyV &b)
{
  CHECK_AND_ASSERT_THROW_MES(a.size() == b.size(), "Incompatible sizes of a and b");
  rct::keyV res(a.size());
  for (size_t i = 0; i < a.size(); ++i)
  {
    sc_mul(res[i].bytes, a[i].bytes, b[i].bytes);
  }
  return res;
}

/* folds a curvepoint array using a two way scaled Hadamard product */
static void hadamard_fold(std::vector<ge_p3> &v, const rct::keyV *scale, const rct::key &a, const rct::key &b)
{
  CHECK_AND_ASSERT_THROW_MES((v.size() & 1) == 0, "Vector size should be even");
  const size_t sz = v.size() / 2;
  for (size_t n = 0; n < sz; ++n)
  {
    ge_dsmp c[2];
    ge_dsm_precomp(c[0], &v[n]);
    ge_dsm_precomp(c[1], &v[sz + n]);
    rct::key sa, sb;
    if (scale) sc_mul(sa.bytes, a.bytes, (*scale)[n].bytes); else sa = a;
    if (scale) sc_mul(sb.bytes, b.bytes, (*scale)[sz + n].bytes); else sb = b;
    ge_double_scalarmult_precomp_vartime2_p3(&v[n], sa.bytes, c[0], sb.bytes, c[1]);
  }
  v.resize(sz);
}

/* Add two vectors */
static rct::keyV vector_add(const rct::keyV &a, const rct::keyV &b)
{
  CHECK_AND_ASSERT_THROW_MES(a.size() == b.size(), "Incompatible sizes of a and b");
  rct::keyV res(a.size());
  for (size_t i = 0; i < a.size(); ++i)
  {
    sc_add(res[i].bytes, a[i].bytes, b[i].bytes);
  }
  return res;
}

/* Subtract two vectors */
static rct::keyV vector_subtract(const rct::keyV &a, const rct::keyV &b)
{
  CHECK_AND_ASSERT_THROW_MES(a.size() == b.size(), "Incompatible sizes of a and b");
  rct::keyV res(a.size());
  for (size_t i = 0; i < a.size(); ++i)
  {
    sc_sub(res[i].bytes, a[i].bytes, b[i].bytes);
  }
  return res;
}

/* Multiply a scalar and a vector */
static rct::keyV vector_scalar(const epee::span<const rct::key> &a, const rct::key &x)
{
  rct::keyV res(a.size());
  for (size_t i = 0; i < a.size(); ++i)
  {
    sc_mul(res[i].bytes, a[i].bytes, x.bytes);
  }
  return res;
}

static rct::keyV vector_scalar(const rct::keyV &a, const rct::key &x)
{
  return vector_scalar(epee::span<const rct::key>(a.data(), a.size()), x);
}

/* Multiply a scalar and a vector */
static rct::keyV vector_scalar(const std::vector<rct::xmr_amount> &a, const rct::key &x)
{
  rct::keyV res(a.size());
  for (size_t i = 0; i < a.size(); ++i)
  {
    sc_mul(res[i].bytes, rct::d2h(a[i]).bytes, x.bytes);
  }
  return res;
}

/* Create a vector from copies of a single value */
static rct::keyV vector_dup(const rct::key &x, size_t N)
{
  return rct::keyV(N, x);
}

static rct::key sm(rct::key y, int n, const rct::key &x)
{
  while (n--)
    sc_mul(y.bytes, y.bytes, y.bytes);
  sc_mul(y.bytes, y.bytes, x.bytes);
  return y;
}


/* Compute the inverse of a scalar, the stupid way */
static rct::key invert(const rct::key &x)
{
  rct::key _1, _10, _100, _11, _101, _111, _1001, _1011, _1111;

  _1 = x;
  sc_mul(_10.bytes, _1.bytes, _1.bytes);
  sc_mul(_100.bytes, _10.bytes, _10.bytes);
  sc_mul(_11.bytes, _10.bytes, _1.bytes);
  sc_mul(_101.bytes, _10.bytes, _11.bytes);
  sc_mul(_111.bytes, _10.bytes, _101.bytes);
  sc_mul(_1001.bytes, _10.bytes, _111.bytes);
  sc_mul(_1011.bytes, _10.bytes, _1001.bytes);
  sc_mul(_1111.bytes, _100.bytes, _1011.bytes);

  rct::key inv;
  sc_mul(inv.bytes, _1111.bytes, _1.bytes);

  inv = sm(inv, 123 + 3, _101);
  inv = sm(inv, 2 + 2, _11);
  inv = sm(inv, 1 + 4, _1111);
  inv = sm(inv, 1 + 4, _1111);
  inv = sm(inv, 4, _1001);
  inv = sm(inv, 2, _11);
  inv = sm(inv, 1 + 4, _1111);
  inv = sm(inv, 1 + 3, _101);
  inv = sm(inv, 3 + 3, _101);
  inv = sm(inv, 3, _111);
  inv = sm(inv, 1 + 4, _1111);
  inv = sm(inv, 2 + 3, _111);
  inv = sm(inv, 2 + 2, _11);
  inv = sm(inv, 1 + 4, _1011);
  inv = sm(inv, 2 + 4, _1011);
  inv = sm(inv, 6 + 4, _1001);
  inv = sm(inv, 2 + 2, _11);
  inv = sm(inv, 3 + 2, _11);
  inv = sm(inv, 3 + 2, _11);
  inv = sm(inv, 1 + 4, _1001);
  inv = sm(inv, 1 + 3, _111);
  inv = sm(inv, 2 + 4, _1111);
  inv = sm(inv, 1 + 4, _1011);
  inv = sm(inv, 3, _101);
  inv = sm(inv, 2 + 4, _1111);
  inv = sm(inv, 3, _101);
  inv = sm(inv, 1 + 2, _11);

#ifdef DEBUG_BP
  rct::key tmp;
  sc_mul(tmp.bytes, inv.bytes, x.bytes);
  CHECK_AND_ASSERT_THROW_MES(tmp == rct::identity(), "invert failed");
#endif
  return inv;
}

static rct::keyV invert(rct::keyV &x)
{
  rct::keyV scratch;
  scratch.reserve(x.size());

  rct::key acc = rct::identity();
  for (size_t n = 0; n < x.size(); ++n)
  {
    scratch.push_back(acc);
    if (n == 0)
      acc = x[0];
    else
      sc_mul(acc.bytes, acc.bytes, x[n].bytes);
  }

  acc = invert(acc);

  rct::key tmp;
  for (int i = x.size(); i-- > 0; )
  {
    sc_mul(tmp.bytes, acc.bytes, x[i].bytes);
    sc_mul(x[i].bytes, acc.bytes, scratch[i].bytes);
    acc = tmp;
  }

  return x;
}

/* Compute the slice of a vector */
static epee::span<const rct::key> slice(const rct::keyV &a, size_t start, size_t stop)
{
  CHECK_AND_ASSERT_THROW_MES(start < a.size(), "Invalid start index");
  CHECK_AND_ASSERT_THROW_MES(stop <= a.size(), "Invalid stop index");
  CHECK_AND_ASSERT_THROW_MES(start < stop, "Invalid start/stop indices");
  return epee::span<const rct::key>(&a[start], stop - start);
}

static rct::key hash_cache_mash(rct::key &hash_cache, const rct::key &mash0)
{
  rct::keyV data;
  data.reserve(2);
  data.push_back(hash_cache);
  data.push_back(mash0);
  return hash_cache = rct::hash_to_scalar(data);
}

static rct::key hash_cache_mash(rct::key &hash_cache, const rct::key &mash0, const rct::key &mash1)
{
  rct::keyV data;
  data.reserve(3);
  data.push_back(hash_cache);
  data.push_back(mash0);
  data.push_back(mash1);
  return hash_cache = rct::hash_to_scalar(data);
}

static rct::key hash_cache_mash(rct::key &hash_cache, const rct::key &mash0, const rct::key &mash1, const rct::key &mash2)
{
  rct::keyV data;
  data.reserve(4);
  data.push_back(hash_cache);
  data.push_back(mash0);
  data.push_back(mash1);
  data.push_back(mash2);
  return hash_cache = rct::hash_to_scalar(data);
}

static rct::key hash_cache_mash(rct::key &hash_cache, const rct::key &mash0, const rct::key &mash1, const rct::key &mash2, const rct::key &mash3)
{
  rct::keyV data;
  data.reserve(5);
  data.push_back(hash_cache);
  data.push_back(mash0);
  data.push_back(mash1);
  data.push_back(mash2);
  data.push_back(mash3);
  return hash_cache = rct::hash_to_scalar(data);
}

struct constraints {
  rct::keyV theta_vec;
  rct::keyV theta_inv_vec;
  rct::keyV mu_vec;
  rct::keyV nu_vec;
  rct::keyV omega_vec;
  rct::keyV alpha_vec;
  rct::keyV beta_vec;
  rct::key delta;
  rct::key kappa;

  constraints(size_t s, size_t n, size_t beta, rct::key y, rct::key z, rct::key u, rct::key v) {
    size_t sn  = s*n;
    size_t m = 2+3*s+beta+n+sn;
    size_t points[] = {1,2,2+n,2+n+s,2+n+s+sn, 2+n+s+sn+beta, m-s, m};

    rct::key tmp;
    auto yN = vector_powers(y, sn+beta);
    auto vS = vector_powers(v, s);
    auto uvS = vector_scalar(vS,u);
    auto z9 = vector_powers(z, 9);
    const rct::keyV twoN = vector_powers(TWO, beta);

    rct::key z27; sc_add(z27.bytes, z9[2].bytes, z9[7].bytes);
    
    theta_vec.assign(m,rct::zero());
    theta_inv_vec.assign(m,rct::zero());
    mu_vec.assign(m,rct::zero());
    nu_vec.assign(m,rct::zero());
    omega_vec.assign(m,rct::zero());
    alpha_vec.assign(m,rct::zero());
    beta_vec.assign(m,rct::zero());
    kappa = rct::zero();
    for(size_t i=0; i<sn+beta; i++) {
      theta_vec[points[3]+i] = yN[i]; 
      sc_mul(nu_vec[points[3]+i].bytes, yN[i].bytes, z9[8].bytes);
      mu_vec[points[3]+i] = nu_vec[points[3]+i]; 
      sc_add(kappa.bytes, nu_vec[points[3]+i].bytes, kappa.bytes);
    }
    mu_vec[0] = z9[4];
    mu_vec[1] = z9[5];
    for(size_t i=0; i<n; ++i) sc_mulsub(mu_vec[points[1]+i].bytes, yN[i].bytes, z9[6].bytes, mu_vec[points[1]+i].bytes);

    for(size_t i=0; i<beta;i++) sc_mul(mu_vec[points[4]+i].bytes, twoN[i].bytes, z27.bytes); 

    for(size_t i=0; i<s;i++) {
      sc_muladd(theta_vec[points[2]+i].bytes, yN[i].bytes, z.bytes, theta_vec[points[2]+i].bytes);
      sc_mul(omega_vec[points[2]+i].bytes, vS[i].bytes, z9[5].bytes);
      for(size_t j=0;j<n;++j) {
        sc_mul(tmp.bytes, vS[i].bytes, yN[j].bytes);
        sc_muladd(mu_vec[points[3]+i*n+j].bytes, yN[i].bytes, z9[3].bytes ,mu_vec[points[3]+i*n+j].bytes);
        sc_muladd(mu_vec[points[3]+i*n+j].bytes, tmp.bytes, z9[6].bytes ,mu_vec[points[3]+i*n+j].bytes);
      }
      sc_mul(mu_vec[points[5]+i].bytes, uvS[i].bytes, z9[4].bytes);
      sc_sub(mu_vec[points[5]+i].bytes,mu_vec[points[5]+i].bytes, z9[7].bytes);
      sc_mul(mu_vec[points[6]+i].bytes, uvS[i].bytes, z9[5].bytes);
    }

    theta_inv_vec = invert(theta_vec);
    rct::key z13; sc_add(z13.bytes, z9[1].bytes, z9[3].bytes);
    for(size_t i=0; i<s; i++) sc_muladd(kappa.bytes, z13.bytes, yN[i].bytes,kappa.bytes);

    alpha_vec = hadamard(vector_add(omega_vec, nu_vec), theta_inv_vec);
    beta_vec = hadamard(theta_inv_vec, mu_vec);
    sc_add(delta.bytes, kappa.bytes, inner_product(alpha_vec, mu_vec).bytes);
  }
};

struct MProvePlus {
  rct::key u;
  rct::key v;
  rct::keyV I_vec; // vector of key images
  rct::key C_res; // commitment to total reserves
  rct::key A; // Commitment to secret vectors
  rct::key S; // Commitment to blinding factors
  rct::key T1; // Commitment to t1
  rct::key T2; // Commitment to t2
  rct::key taux; // evaluation of t(x) at challenge point 
  rct::key r; // blinding factor for synthetic commitment to t(x)
  rct::key t_hat; // blinding factor for synthetic commitment to inner product
  // inner product argument
  rct::keyV L;
  rct::keyV R;
  rct::key a;
  rct::key b;

  MProvePlus() {}
  MProvePlus(const rct::key &u, const rct::key &v, const rct::keyV &I_vec, const rct::key &C_res, const rct::key &A, const rct::key &S, const rct::key &T1, const rct::key &T2, const rct::key &taux, const rct::key &r, const rct::key &t_hat, const rct::keyV& L, const rct::keyV &R, const rct::key &a, const rct::key &b):
  u(u), v(v), I_vec(I_vec), C_res(C_res), A(A), S(S), T1(T1), T2(T2), taux(taux), r(r), t_hat(t_hat), L(L), R(R), a(a), b(b) {}
};

class MoneroExchange
{
    size_t n;
    size_t s;
    rct::keyV C_vec; // vector of commitments
    rct::keyV P_vec; // vector of public keys(addresses)
    rct::keyV H_vec; // hash of addresses
    rct::keyV E_vec; // secret indices. E[i]=1 if ith address is owned else 0
    rct::keyV x_vec; // secret keys
    rct::key gamma;  // blinding factor of total reserves
    std::vector<rct::xmr_amount> a_vec; // amounts in own addresses
    rct::xmr_amount a_res;
    rct::keyV r_vec; // blinding factors for amounts
    rct::xmr_amount m_maxAmount = 1000; // Only for generating random amounts per address
    MProvePlus m_proof;
  public:
    MoneroExchange(size_t anonSetSize, size_t ownkeysSetSize);
    MProvePlus GenerateProofOfAssets();
    size_t ProofSize();
    MProvePlus GetProof();
    rct::keyV GetC_vec();
    rct::keyV GetH_vec();
    rct::keyV GetP_vec();
    void PrintExchangeState();
};

MoneroExchange::MoneroExchange(size_t anonSetSize, size_t ownkeysSetSize)
{
  n = anonSetSize;
  s = ownkeysSetSize;
  C_vec = rct::keyV(anonSetSize);
  P_vec = rct::keyV(anonSetSize);
  H_vec = rct::keyV(anonSetSize);
  E_vec = rct::keyV(anonSetSize);
  x_vec = rct::keyV(ownkeysSetSize);
  a_vec = std::vector<rct::xmr_amount>(ownkeysSetSize);
  r_vec = rct::keyV(ownkeysSetSize);

  // select the indices for ownkeys
  // std::ranges::sample(std::views::iota(0, anonSetSize), idx, ownkeysSetSize, std::mt19937{std::random_device{}()});
  std::vector<size_t> idx(anonSetSize);
  std::iota(idx.begin(), idx.end(),0);
  for(auto i: idx) std::cout<<i<<' ';
  std::cout<<std::endl;
  // std::random_shuffle(idx.begin(),idx.end());
  std::shuffle(idx.begin(), idx.end(), std::mt19937{std::random_device{}()});
  idx.resize(ownkeysSetSize);
  std::sort(idx.begin(), idx.end());
  std::cout<<"Indices: ";
  for(auto i: idx) std::cout<<i<<' ';
  std::cout<<std::endl;
  gamma = rct::skGen();
  
  a_res = 0;
  size_t index = 0;
  for (size_t i = 0; i < anonSetSize; i++)
  {
    if (index < ownkeysSetSize && i == idx[index])
    {
      ge_p3 Hi_p3;
      a_vec[index] = rct::randXmrAmount(m_maxAmount);
      r_vec[index] = rct::skGen();
      rct::skpkGen(x_vec[index], P_vec[i]);
      hash_to_p3(Hi_p3, P_vec[i]);
      ge_p3_tobytes(H_vec[i].bytes, &Hi_p3);
      C_vec[i] = rct::commit(a_vec[index], r_vec[index]);
      E_vec[i] = rct::identity();
      a_res += a_vec[index];
      index++;
    }
    else
    {
      P_vec[i] = rct::pkGen();
      H_vec[i] = rct::pkGen();
      C_vec[i] = rct::pkGen();
      E_vec[i] = rct::zero();
    }
  }
}

MProvePlus MoneroExchange::GenerateProofOfAssets()
{
    // Computing beta
  size_t beta = 0;
  for(beta=0;(1ul<<beta)<a_res;beta++);
  
  //Calculating various sizes
  size_t sn = s*n;
  size_t m = 2+3*s+beta+n+sn;
  size_t logm;
  for(logm=0; m>(1ul<<logm); logm++);
  beta = beta + (1ul<<logm) - m;
  m = (1ul<<logm);
  init_exponents(1ul<<logm);
  
  // u,v
  rct::key hashcache = rct::skGen();
  auto u = hash_cache_mash(hashcache, rct::hash_to_scalar(Gi));;
  auto v = hashcache = hash_cache_mash(hashcache, rct::hash_to_scalar(Hi));
  rct::key usq, minus_u, minus_usq;
  auto vS = vector_powers(v,s);
  sc_mul(usq.bytes, u.bytes, u.bytes);
  sc_sub(minus_u.bytes, rct::zero().bytes, u.bytes);
  sc_sub(minus_usq.bytes, rct::zero().bytes, usq.bytes);

  std::cout<<"Creating u,v successful"<<std::endl;
  std::cout<<"u: "<<u<<std::endl;
  std::cout<<"v: "<<v<<std::endl;
  

  // Computing b
  rct::keyV b_vec(beta);
  rct::keyV b_vec_comp(beta);
  for (size_t i = beta; i-- > 0;)
  {
    if (a_res & (((uint64_t)1)<<i)) {
      b_vec[i] = rct::identity();
      b_vec_comp[i] = rct::zero();
    }
    else {
      b_vec_comp[i] = rct::identity();
      b_vec[i] = rct::zero();
    }
  }

  uint64_t test_a = 0;
  for(size_t i=0; i<beta; i++) {
    if(b_vec[i]==rct::identity()) {
      test_a += ((uint64_t)1)<<i;
    }
  }
  CHECK_AND_ASSERT_THROW_MES(test_a == a_res, "test_aL failed");
  std::cout<<"Creating b successful"<<std::endl;

  //Bases
  std::vector<ge_p3> Q_p3(Gi_p3.begin(), Gi_p3.begin()+2+n+s);
  std::vector<ge_p3> G_prime_p3(Gi_p3.begin()+2+n+s, Gi_p3.begin()+m);
  std::vector<ge_p3> H_p3(Hi_p3.begin(), Hi_p3.end());
  std::cout<<"expected size = "<<m<<std::endl;
  std::cout<<"Creating bases successful"<<std::endl;

  // Computing C_res, ehat, vec(E), I_vec
  rct::keyV ehat(n);
  rct::keyV E_mat(sn), E_mat_comp(sn);
  rct::keyV I_vec(s);
  rct::key C_res = rct::commit(a_res, gamma);
  // sc_mul(C_res.bytes, gamma.bytes, rct::G.bytes);
  //  = rct::scalarmultBase(gamma);
  size_t index=0;
  for(size_t i=0;i<n;i++) {
    if(sc_isnonzero(E_vec[i].bytes) == 1) {
      E_mat[n*index+i] = rct::identity();
      ehat[i] = vS[index];
      // sc_mul(C_res.bytes, C_res.bytes, C_vec[i].bytes);
      // sc_add(gamma.bytes, gamma.bytes, r_vec[index].bytes);
      I_vec[index] = rct::scalarmultKey(H_vec[i],  x_vec[index]);
      index = index+1;
    } 
    else E_mat_comp[n*index+i] = rct::identity();
  }
  std::cout<<"Creating C_res, ehat, vec(E), I_vec successful"<<std::endl;
  
  // computing xi
  rct::keyV a_vec_key(a_vec.size());
  for(size_t i=0; i<a_vec.size();i++) a_vec_key[i] = d2h(a_vec[i]);
  rct::key xi = inner_product(vS, a_vec_key);
  sc_mul(xi.bytes, xi.bytes, minus_u.bytes);
  std::cout<<"Creating xi successful"<<std::endl;
  
  //computing eta
  rct::key eta;
  sc_mul(eta.bytes, inner_product(vS, r_vec).bytes, minus_u);
  sc_sub(eta.bytes, eta.bytes, inner_product(vS, x_vec).bytes);
  std::cout<<"Creating eta successful"<<std::endl;
  
  // computing inverse of x
  rct::keyV x_inv = invert(x_vec);
  std::cout<<"Creating x_inv successful"<<std::endl;

  // Secret vectors
  //cL = [xi, eta, e_hat, x_inv, E_mat, b, a, r]
  rct::keyV cL;
  cL.reserve(m);
  cL.emplace_back(xi);  
  cL.emplace_back(eta);  
  std::copy(ehat.begin(), ehat.end(), std::back_inserter(cL));
  std::copy(x_inv.begin(), x_inv.end(), std::back_inserter(cL));
  std::copy(E_mat.begin(), E_mat.end(), std::back_inserter(cL));
  std::copy(b_vec.begin(), b_vec.end(), std::back_inserter(cL));
  for(auto &i: a_vec_key) cL.push_back(i);
  std::copy(r_vec.begin(), r_vec.end(), std::back_inserter(cL));
  std::cout<<"Creating cL successful "<<cL.size()<<std::endl;

  //cR = [0^{2+n}, x, 1-E_mat, 1-b, 0^2s]
  rct::keyV cR(2+n, rct::zero());
  cR.reserve(m);
  std::copy(x_vec.begin(), x_vec.end(), std::back_inserter(cR));
  std::copy(E_mat_comp.begin(), E_mat_comp.end(), std::back_inserter(cR));
  std::copy(b_vec_comp.begin(), b_vec_comp.end(), std::back_inserter(cR));
  std::fill_n(std::back_inserter(cR),2*s,rct::zero());
  std::cout<<"Creating cR successful "<<cR.size()<<std::endl;

  //Computing G0
  std::vector<ge_p3> G0_p3(m);  std::copy_n(Gi_p3.begin(), m, G0_p3.begin());
  std::cout<<"Creating G0 successful"<<std::endl;
  
  try_again:
    //Computing A
    rct::key rA = rct::skGen();
    rct::key A = cross_vector_exponent(m,G0_p3,0,H_p3,0,cL,0,cR,0,NULL,&F_p3,&rA);
    std::cout<<"Creating A successful"<<std::endl;

    //Challenge w
    rct::key w_G = hashcache= hash_cache_mash(hashcache, A);
    if(w_G==rct::zero()) goto try_again;
    std::cout<<"Creating wG successful"<<std::endl;
    std::cout<<"wG: "<<w_G<<std::endl;

    // Computing Gw
    rct::key uw, usqw, minus_usqw;
    sc_mul(uw.bytes, u.bytes, w_G.bytes);
    sc_mul(usqw.bytes, usq.bytes, w_G.bytes);
    sc_mul(minus_usqw.bytes, w_G.bytes, minus_usq.bytes);
    std::vector<ge_p3> Gw_p3(2+n+s);
    rct::geDsmp C_ge, P_ge, H_ge;
    rct::key tmp, tmp2;
    ge_p3 p2;
    ge_p1p1 p1;
    ge_double_scalarmult_base_vartime_p3(&Gw_p3[0], w_G.bytes, &Q_p3[0], rct::identity().bytes);
    ge_cached Q_cache, H_cache; ge_p3_to_cached(&Q_cache, &Q_p3[1]); ge_p3_to_cached(&H_cache, &ge_p3_H);
    ge_double_scalarmult_precomp_vartime2_p3(&Gw_p3[1], w_G.bytes, &H_cache, rct::identity().bytes, &Q_cache);
    for(size_t i=0;i<n;i++) { 
      rct::precomp(C_ge.k, C_vec[i]);
      rct::precomp(H_ge.k, H_vec[i]);
      rct::precomp(P_ge.k, P_vec[i]);
      rct::addKeys_aAbBcC(tmp, uw, C_ge.k, usqw, H_ge.k, w_G, P_ge.k);
      CHECK_AND_ASSERT_THROW_MES(ge_frombytes_vartime(&p2, tmp.bytes) == 0, "ge_frombytes_vartime failed at Yhat");
      ge_p3_to_cached(&Q_cache, &Q_p3[2+i]);
      ge_add(&p1, &p2, &Q_cache);
      ge_p1p1_to_p3(&Gw_p3[2+i], &p1);
    }
    std::cout<<"Creating Yhat successful"<<std::endl;
    // Computing Ihat
    for(size_t i=0; i<s; i++) {
      sc_mul(tmp2.bytes, vS[i].bytes, minus_usq.bytes);
      ge_p3_to_cached(&Q_cache, &Q_p3[2+n+i]);
      rct::addKeys3(tmp, tmp2, I_vec[i], rct::identity(), &Q_cache);
      CHECK_AND_ASSERT_THROW_MES(ge_frombytes_vartime(&Gw_p3[2+n+i], tmp.bytes) == 0, "ge_frombytes_vartime failed at Ihat");
    }
    std::copy(G_prime_p3.begin(), G_prime_p3.end(), std::back_inserter(Gw_p3));
    std::cout<<"Creating Gw successful"<<std::endl;

    // Check if G_w^c_L = G_0^cL or G_w^cL G_0^{-cL} = 1
    // #ifdef DEBUG_MP
      rct::keyV minus_cL = vector_subtract(vector_dup(rct::zero(),m),cL);
      rct::key test_G0 = cross_vector_exponent(0, Gw_p3, 0, G0_p3, 0, cL, 0, minus_cL, 0, NULL, NULL, NULL);
      CHECK_AND_ASSERT_THROW_MES(test_G0 == rct::identity(), "test_G0 failed");
    // #endif
    // sL, sR
    rct::keyV sL = rct::skvGen(m);
    rct::keyV sR(m);
    for(size_t i=0;i<m;i++) 
      if(cR[i] == rct::zero()) sR[i]= rct::zero();
      else sR[i] = rct::skGen();
    std::cout<<"Creating sL,sR successful"<<std::endl;

    //Computing S: commitment to sL, sR
    rct::key rS = rct::skGen();
    rct::key S = cross_vector_exponent(0, Gw_p3, 0, H_p3, 0, sL, 0,sR, 0, NULL, &F_p3, &rS);
    std::cout<<"Creating S successful"<<std::endl;

    //get y,z
    rct::key y = hash_cache_mash(hashcache, S);
    rct::key z = hashcache = hash_cache_mash(hashcache, S, y);
    rct::key zsq;
    std::cout<<"Creating y,z successful"<<std::endl;
    std::cout<<"y: "<<y<<std::endl;
    std::cout<<"z: "<<z<<std::endl;

    sc_mul(zsq.bytes, z.bytes,z.bytes);
    if(y==rct::zero() || z==rct::zero()) goto try_again;
    
    // Constraints
    constraints constraint_vec(s, n, beta, y, z, u, v);
    std::cout<<"Creating constraints successful"<<std::endl;
    
    //Constructing the polynomial l,r,t
    rct::keyV l0 = vector_add(cL, constraint_vec.alpha_vec);
    rct::keyV &l1 = sL;
    rct::keyV r0 = hadamard(constraint_vec.theta_vec, cR);
    r0 = vector_add(r0, constraint_vec.mu_vec);
    rct::keyV r1 = hadamard(constraint_vec.theta_vec, sR);
    rct::key t1_1 = inner_product(l0, r1);
    rct::key t1_2 = inner_product(l1, r0);
    rct::key t1;
    sc_add(t1.bytes, t1_1.bytes, t1_2.bytes);
    rct::key t2 = inner_product(l1, r1);      
    std::cout<<"Creating l,r,t successful"<<std::endl;

    //Commitments to t1,t2
    rct::key tau1 = rct::skGen(), tau2 = rct::skGen();
    ge_p3 p3;
    rct::key T1, T2;
    ge_double_scalarmult_base_vartime_p3(&p3, t1.bytes, &ge_p3_H, tau1.bytes);
    ge_p3_tobytes(T1.bytes, &p3);
    ge_double_scalarmult_base_vartime_p3(&p3, t2.bytes, &ge_p3_H, tau2.bytes);
    ge_p3_tobytes(T2.bytes, &p3);
    std::cout<<"Creating T1,T2 successful"<<std::endl;

    //computing tau, r
    rct::key x = hash_cache_mash(hashcache, z, T1, T2);
    if (x == rct::zero())    goto try_again;
    rct::key taux;
    sc_mul(taux.bytes, tau1.bytes, x.bytes);
    rct::key xsq;
    sc_mul(xsq.bytes, x.bytes, x.bytes);
    sc_muladd(taux.bytes, tau2.bytes, xsq.bytes, taux.bytes);
    sc_muladd(taux.bytes, gamma.bytes, zsq.bytes, taux.bytes);
    rct::key r;
    sc_muladd(r.bytes, rS.bytes, x.bytes, rA.bytes);
    std::cout<<"Creating taux,r successful"<<std::endl;
    std::cout<<"x: "<<x<<std::endl;
    //evaluating l(x), r(x)
    rct::keyV l_x = l0;
    l_x = vector_add(l_x, vector_scalar(l1,x));
    rct::keyV r_x = r0;
    r_x = vector_add(r_x, vector_scalar(r1,x));
    std::cout<<"Creating l(x),r(x) successful"<<std::endl;

    //computing t_hat
    rct::key t_hat = inner_product(l_x, r_x);
    std::cout<<"Creating t_hat successful"<<std::endl;
    rct::key test_t;
    const rct::key t0 = inner_product(l0, r0);
    sc_muladd(test_t.bytes, t1.bytes, x.bytes, t0.bytes);
    sc_muladd(test_t.bytes, t2.bytes, xsq.bytes, test_t.bytes);
    CHECK_AND_ASSERT_THROW_MES(test_t == t_hat, "test_t check failed");

    //inner product argument
    rct::key x_ip = hash_cache_mash(hashcache, x, taux, r, t_hat);
    if (x_ip == rct::zero()) goto try_again;
    std::cout<<"Creating x_ip successful"<<std::endl;
    std::cout<<"x_ip: "<<x_ip<<std::endl;

    // These are used in the inner product rounds
    size_t nprime = 1ul<<logm;
    std::vector<ge_p3> Gprime(nprime);
    std::vector<ge_p3> Hprime(nprime);
    rct::keyV aprime(nprime);
    rct::keyV bprime(nprime);
    for (size_t i = 0; i < nprime; ++i)
    {
      Gprime[i] = Gw_p3[i];
      Hprime[i] = H_p3[i];
      aprime[i] = l_x[i];
      bprime[i] = r_x[i];
    }
    rct::keyV L(logm);
    rct::keyV R(logm);
    int round = 0;
    rct::keyV w(logm); // this is the challenge x in the inner product protocol

    const rct::keyV *scale =  &constraint_vec.theta_inv_vec;
    while (nprime > 1)
    {
      // PAPER LINE 20
      nprime /= 2;

      // PAPER LINES 21-22
      rct::key cL_ip = inner_product(slice(aprime, 0, nprime), slice(bprime, nprime, bprime.size()));
      rct::key cR_ip = inner_product(slice(aprime, nprime, aprime.size()), slice(bprime, 0, nprime));

      // PAPER LINES 23-24
      sc_mul(tmp.bytes, cL_ip.bytes, x_ip.bytes);
      L[round] = cross_vector_exponent(nprime, Gprime, nprime, Hprime, 0, aprime, 0, bprime, nprime, scale, &ge_p3_H, &tmp);
      sc_mul(tmp.bytes, cR_ip.bytes, x_ip.bytes);
      R[round] = cross_vector_exponent(nprime, Gprime, 0, Hprime, nprime, aprime, nprime, bprime, 0, scale, &ge_p3_H, &tmp);

      // PAPER LINES 25-27
      w[round] = hash_cache_mash(hashcache, L[round], R[round]);
      if (w[round] == rct::zero()) goto try_again;

        // PAPER LINES 29-30
      const rct::key winv = invert(w[round]);
      if (nprime > 1)
      {
        hadamard_fold(Gprime, NULL, winv, w[round]);
        hadamard_fold(Hprime, scale, w[round], winv);
      }

      // PAPER LINES 33-34
      aprime = vector_add(vector_scalar(slice(aprime, 0, nprime), w[round]), vector_scalar(slice(aprime, nprime, aprime.size()), winv));
      bprime = vector_add(vector_scalar(slice(bprime, 0, nprime), winv), vector_scalar(slice(bprime, nprime, bprime.size()), w[round]));

      scale = NULL;
      ++round;
    }

    m_proof = MProvePlus(u, v, I_vec, C_res, A, S, T1, T2, taux, r, t_hat, L, R, aprime[0], bprime[0]);
    return m_proof;
}

size_t MoneroExchange::ProofSize()
{
  size_t beta = 0;
  for(beta=0;(1ul<<beta)<a_res;beta++);
  size_t logm, m = 2+3*s+beta+n+s*n;
  for(logm=0; (1ul<<logm)<m; logm++);
  
  size_t psize = 0;
  psize += s*32; // m_proof.I_vec
  psize += 32*10; // m_proof.c_res, m_proof.A,  m_proof.S,  m_proof.T1,  m_proof.T2,  m_proof.taux, m_proof.r,  m_proof.t_hat,  m_proof.a,  m_proof.b  
  psize += 32*2*logm; // m_proof.L, mproof.R

  return psize;
}

MProvePlus MoneroExchange::GetProof()
{
  return m_proof;
}

rct::keyV MoneroExchange::GetC_vec() {
  return C_vec;
}

rct::keyV MoneroExchange::GetP_vec() {
  return P_vec;
}

rct::keyV MoneroExchange::GetH_vec() {
  return H_vec;
}

void MoneroExchange::PrintExchangeState()
{
  std::cout << "Anonymity set size = " << n << std::endl;
  std::cout << "Own keys set size = " << s << std::endl;
  std::cout << std::endl;
  size_t index = 1;
  for (size_t i = 0; i < n; i++)
  {
    if(sc_isnonzero(E_vec[i].bytes) == 1)
    {
      std::cout << "Address at index " << i+1 << " is exchange owned" << std::endl;
      std::cout << "Address is " << index << " out of " << s << std::endl;
      std::cout << "Key Image is " << m_proof.I_vec[i] << std::endl;
      std::cout << "Amount in address is " << a_vec[i] << std::endl;
      std::cout << std::endl;
      index += 1;
    }
  }
}

bool MProveProofPublicVerification(MProvePlus proof, rct::keyV C_vec, rct::keyV P_vec, rct::keyV H_vec) 
{
  CHECK_AND_ASSERT_MES(proof.L.size() == proof.R.size(), false, "Mismatched L and R");
  CHECK_AND_ASSERT_MES(proof.L.size() > 0, false, "Empty proof");
  size_t length = proof.L.size();
  size_t m = 1u<<length;
  init_exponents(m);
  
  size_t n = C_vec.size(), s = proof.I_vec.size();
  size_t sn = s*n;
  size_t beta = m - (2+3*s+n+sn);
  
  //Bases
  std::vector<ge_p3> Q_p3(Gi_p3.begin(), Gi_p3.begin()+2+n+s);
  std::vector<ge_p3> G_prime_p3(Gi_p3.begin()+2+n+s, Gi_p3.begin()+m);
  std::vector<ge_p3> H_p3(Hi_p3.begin(), Hi_p3.end());

  rct::key weight = rct::skGen(); // constant c in final verification equation

  //Reconstructing challenges
  rct::key hashcache;
  auto u = proof.u;
  auto v = hashcache = proof.v;
  
  rct::key usq, minus_usq;
  sc_mul(usq.bytes, u.bytes, u.bytes);
  sc_sub(minus_usq.bytes, rct::zero().bytes, usq.bytes);
  auto vS = vector_powers(v,s);
  std::cout<<"u: "<<u<<std::endl;
  std::cout<<"v: "<<v<<std::endl;
  
  rct::key w_G = hashcache= hash_cache_mash(hashcache, proof.A);
  CHECK_AND_ASSERT_MES(!(w_G == rct::zero()), false, "w_G == 0");
  std::cout<<"w_G: "<<w_G<<std::endl;

  rct::key y = hash_cache_mash(hashcache, proof.S);
  CHECK_AND_ASSERT_MES(!(y == rct::zero()), false, "y == 0");
  std::cout<<"y: "<<y<<std::endl;

  rct::key z = hashcache = hash_cache_mash(hashcache, proof.S, y);
  CHECK_AND_ASSERT_MES(!(z == rct::zero()), false, "z == 0");
  std::cout<<"z: "<<z<<std::endl;
  
  rct::key x = hash_cache_mash(hashcache, z, proof.T1, proof.T2);
  CHECK_AND_ASSERT_MES(!(x == rct::zero()), false, "x == 0");
  std::cout<<"x: "<<x<<std::endl;

  rct::key x_ip = hash_cache_mash(hashcache, x, proof.taux, proof.r, proof.t_hat);
  CHECK_AND_ASSERT_MES(!(x_ip == rct::zero()), false, "x_ip == 0");
  std::cout<<"x_ip: "<<x_ip<<std::endl;

  rct::keyV w(length);
  for (size_t i = 0; i < length; ++i)
  {
    w[i] = hash_cache_mash(hashcache, proof.L[i], proof.R[i]);
    CHECK_AND_ASSERT_MES(!(w[i] == rct::zero()), false, "w[i] == 0");
  }
  rct::keyV winv = invert(w);
  
  // //Getting constraints vector
  constraints constraint_vec(s, n, beta, y, z, u, v);

  // Computing Gw
  rct::key uw, usqw, minus_usqw;
  sc_mul(uw.bytes, u.bytes, w_G.bytes);
  sc_mul(usqw.bytes, usq.bytes, w_G.bytes);
  sc_mul(minus_usqw.bytes, w_G.bytes, minus_usq.bytes);
  std::vector<ge_p3> Gw_p3(2+n+s);
  rct::geDsmp C_ge, P_ge, H_ge;
  rct::key tmp, tmp2;
  ge_p3 p2;
  ge_p1p1 p1;
  ge_double_scalarmult_base_vartime_p3(&Gw_p3[0], w_G.bytes, &Q_p3[0], rct::identity().bytes);
  ge_cached Q_cache, H_cache; ge_p3_to_cached(&Q_cache, &Q_p3[1]); ge_p3_to_cached(&H_cache, &ge_p3_H);
  ge_double_scalarmult_precomp_vartime2_p3(&Gw_p3[1], w_G.bytes, &H_cache, rct::identity().bytes, &Q_cache);
  for(size_t i=0;i<n;i++) { 
    rct::precomp(C_ge.k, C_vec[i]);
    rct::precomp(H_ge.k, H_vec[i]);
    rct::precomp(P_ge.k, P_vec[i]);
    rct::addKeys_aAbBcC(tmp, uw, C_ge.k, usqw, H_ge.k, w_G, P_ge.k);
    CHECK_AND_ASSERT_THROW_MES(ge_frombytes_vartime(&p2, tmp.bytes) == 0, "ge_frombytes_vartime failed at Yhat");
    ge_p3_to_cached(&Q_cache, &Q_p3[2+i]);
    ge_add(&p1, &p2, &Q_cache);
    ge_p1p1_to_p3(&Gw_p3[2+i], &p1);
  }
  // Computing Ihat
  for(size_t i=0; i<s; i++) {
    sc_mul(tmp2.bytes, vS[i].bytes, minus_usq.bytes);
    ge_p3_to_cached(&Q_cache, &Q_p3[2+n+i]);
    rct::addKeys3(tmp, tmp2, proof.I_vec[i], rct::identity(), &Q_cache);
    CHECK_AND_ASSERT_THROW_MES(ge_frombytes_vartime(&Gw_p3[2+n+i], tmp.bytes) == 0, "ge_frombytes_vartime failed at Ihat");
  }
  std::copy(G_prime_p3.begin(), G_prime_p3.end(), std::back_inserter(Gw_p3));
  
  std::cout<<"Creating Gw successful"<<std::endl;
  std::vector<rct::MultiexpData> multiexp_data;
  multiexp_data.reserve(2*m + 2*length + 8);
  
  rct::keyV w_cache(m);
  w_cache[0] = winv[0];
  w_cache[1] = w[0];
  for (size_t j = 1; j < length; ++j)
  {
    const size_t slots = 1<<(j+1);
    for (size_t s = slots; s-- > 0; --s)
    {
      sc_mul(w_cache[s].bytes, w_cache[s/2].bytes, w[j].bytes);
      sc_mul(w_cache[s-1].bytes, w_cache[s/2].bytes, winv[j].bytes);
    }
  }

  // // Gw^{alpha - as} H^{beta - b(theta o s)^{-1}}
  for(size_t i=0; i < m; i++) {
    rct::key g_scalar = proof.a;
    rct::key h_scalar = proof.b;

    // Convert the index to binary IN REVERSE and construct the scalar exponent
    sc_mul(g_scalar.bytes, g_scalar.bytes, w_cache[i].bytes);
    sc_mul(h_scalar.bytes, h_scalar.bytes, w_cache[(~i) & (m-1)].bytes); 
    sc_sub(g_scalar.bytes, constraint_vec.alpha_vec[i].bytes, g_scalar.bytes);
    sc_mul(h_scalar.bytes, h_scalar.bytes, constraint_vec.theta_inv_vec[i].bytes);
    sc_sub(h_scalar.bytes, constraint_vec.beta_vec[i].bytes, h_scalar.bytes);
    multiexp_data.emplace_back(g_scalar, Gw_p3[i]);
    multiexp_data.emplace_back(h_scalar, H_p3[i]);
  }
  std::cout<<"Creating G_vec,H_vec successful"<<std::endl;

  // // Lj^{wj^2} Rj^{wj^-2}
  
  for (size_t i = 0; i < length; ++i)
  {
    sc_mul(tmp.bytes, w[i].bytes, w[i].bytes);
    multiexp_data.emplace_back(tmp, proof.L[i]);
    sc_mul(tmp.bytes, winv[i].bytes, winv[i].bytes);
    multiexp_data.emplace_back(tmp, proof.R[i]);
  }
  std::cout<<"Creating L,R successful"<<std::endl;

  rct::key y0 = rct::zero(), y1 = rct::zero(), y2 = rct::zero(), y3=rct::zero();
  // g^{x_ip(t_hat - ab) - c.taux} Note that U = G^x_ip
  sc_mul(tmp.bytes, proof.a.bytes, proof.b.bytes);
  sc_sub(tmp.bytes, proof.t_hat.bytes, tmp.bytes);
  sc_mul(y0.bytes, tmp.bytes, x_ip.bytes);
  sc_mul(tmp.bytes, weight.bytes, proof.taux.bytes);
  sc_sub(y0.bytes, y0.bytes, tmp.bytes);
  multiexp_data.emplace_back(y0, rct::G);

  // // F^-r
  sc_sub(y1.bytes, rct::zero().bytes, proof.r.bytes);
  multiexp_data.emplace_back(y1, F_p3);
  std::cout<<"Creating F successful"<<std::endl;

  // // S^x
  multiexp_data.emplace_back(x, proof.S);
  std::cout<<"Creating S successful"<<std::endl;

  // // H^{c(delta-t_hat)}
  sc_sub(y2.bytes, constraint_vec.delta.bytes, proof.t_hat.bytes);
  sc_mul(y2.bytes, y2.bytes, weight.bytes);
  multiexp_data.emplace_back(y2, rct::H);
  std::cout<<"Creating H successful"<<std::endl;

  // // T1^cx
  sc_mul(y2.bytes, x.bytes, weight.bytes);
  multiexp_data.emplace_back(y2, proof.T1);
  std::cout<<"Creating T1 successful"<<std::endl;
  
  // // T2^{cx^2}
  rct::key xsq;
  sc_mul(xsq.bytes, x.bytes, x.bytes);
  sc_mul(xsq.bytes, xsq.bytes, weight.bytes);
  multiexp_data.emplace_back(xsq, proof.T2);
  std::cout<<"Creating T2 successful"<<std::endl;

  // C_res^{cz^2}
  rct::key zsq;
  sc_mul(zsq.bytes, z.bytes,z.bytes);
  sc_mul(y3.bytes, zsq.bytes, weight.bytes);
  multiexp_data.emplace_back(y3, proof.C_res);
  std::cout<<"Creating Cres successful"<<std::endl;

  multiexp_data.emplace_back(rct::identity(), proof.A);

  if(!(multiexp(multiexp_data, 0) == rct::identity() )) {
    MERROR("Verification failure");
    return false;
  }
  return true;
}
