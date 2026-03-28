// Lean compiler output
// Module: Std.Net.Addr
// Imports: public import Init.System.IO public import Init.Data.Vector.Basic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_instDecidableEqUInt8___boxed(lean_object*, lean_object*);
uint8_t l_Array_instDecidableEqImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqUInt16___boxed(lean_object*, lean_object*);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Net_instInhabitedMACAddr_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Net_instInhabitedMACAddr_default___closed__0;
static lean_once_cell_t l_Std_Net_instInhabitedMACAddr_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Net_instInhabitedMACAddr_default___closed__1;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedMACAddr_default;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedMACAddr;
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqMACAddr_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqMACAddr_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqMACAddr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqMACAddr___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Net_instInhabitedIPv4Addr_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Net_instInhabitedIPv4Addr_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedIPv4Addr_default;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedIPv4Addr;
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPv4Addr_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPv4Addr_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPv4Addr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPv4Addr___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Net_instInhabitedSocketAddressV4_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Std_Net_instInhabitedSocketAddressV4_default___closed__0;
static lean_once_cell_t l_Std_Net_instInhabitedSocketAddressV4_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Net_instInhabitedSocketAddressV4_default___closed__1;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedSocketAddressV4_default;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedSocketAddressV4;
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddressV4_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddressV4_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddressV4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddressV4___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Net_instInhabitedIPv6Addr_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Net_instInhabitedIPv6Addr_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedIPv6Addr_default;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedIPv6Addr;
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPv6Addr_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPv6Addr_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPv6Addr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPv6Addr___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Net_instInhabitedSocketAddressV6_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Net_instInhabitedSocketAddressV6_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedSocketAddressV6_default;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedSocketAddressV6;
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddressV6_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddressV6_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddressV6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddressV6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v4_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v4_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v6_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v6_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Net_instInhabitedIPAddr_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Net_instInhabitedIPAddr_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedIPAddr_default;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedIPAddr;
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPAddr_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPAddr_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPAddr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPAddr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v4_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v4_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v6_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v6_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Net_instInhabitedSocketAddress_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Net_instInhabitedSocketAddress_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedSocketAddress_default;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedSocketAddress;
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddress_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddress_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddress(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddress___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Net_instInhabitedAddressFamily_default;
LEAN_EXPORT uint8_t l_Std_Net_instInhabitedAddressFamily;
LEAN_EXPORT uint8_t l_Std_Net_AddressFamily_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqAddressFamily(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqAddressFamily___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_ofParts(uint8_t, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_ofParts___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_pton_v4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_ofString___boxed(lean_object*);
lean_object* lean_uv_ntop_v4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_toString___boxed(lean_object*);
static const lean_closure_object l_Std_Net_IPv4Addr_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Net_IPv4Addr_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Net_IPv4Addr_instToString___closed__0 = (const lean_object*)&l_Std_Net_IPv4Addr_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Net_IPv4Addr_instToString = (const lean_object*)&l_Std_Net_IPv4Addr_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_instCoeIPAddr___lam__0(lean_object*);
static const lean_closure_object l_Std_Net_IPv4Addr_instCoeIPAddr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Net_IPv4Addr_instCoeIPAddr___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Net_IPv4Addr_instCoeIPAddr___closed__0 = (const lean_object*)&l_Std_Net_IPv4Addr_instCoeIPAddr___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Net_IPv4Addr_instCoeIPAddr = (const lean_object*)&l_Std_Net_IPv4Addr_instCoeIPAddr___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV4_instCoeSocketAddress___lam__0(lean_object*);
static const lean_closure_object l_Std_Net_SocketAddressV4_instCoeSocketAddress___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Net_SocketAddressV4_instCoeSocketAddress___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Net_SocketAddressV4_instCoeSocketAddress___closed__0 = (const lean_object*)&l_Std_Net_SocketAddressV4_instCoeSocketAddress___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Net_SocketAddressV4_instCoeSocketAddress = (const lean_object*)&l_Std_Net_SocketAddressV4_instCoeSocketAddress___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_ofParts(uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_ofParts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_pton_v6(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_ofString___boxed(lean_object*);
lean_object* lean_uv_ntop_v6(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_toString___boxed(lean_object*);
static const lean_closure_object l_Std_Net_IPv6Addr_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Net_IPv6Addr_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Net_IPv6Addr_instToString___closed__0 = (const lean_object*)&l_Std_Net_IPv6Addr_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Net_IPv6Addr_instToString = (const lean_object*)&l_Std_Net_IPv6Addr_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_instCoeIPAddr___lam__0(lean_object*);
static const lean_closure_object l_Std_Net_IPv6Addr_instCoeIPAddr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Net_IPv6Addr_instCoeIPAddr___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Net_IPv6Addr_instCoeIPAddr___closed__0 = (const lean_object*)&l_Std_Net_IPv6Addr_instCoeIPAddr___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Net_IPv6Addr_instCoeIPAddr = (const lean_object*)&l_Std_Net_IPv6Addr_instCoeIPAddr___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV6_instCoeSocketAddress___lam__0(lean_object*);
static const lean_closure_object l_Std_Net_SocketAddressV6_instCoeSocketAddress___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Net_SocketAddressV6_instCoeSocketAddress___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Net_SocketAddressV6_instCoeSocketAddress___closed__0 = (const lean_object*)&l_Std_Net_SocketAddressV6_instCoeSocketAddress___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Net_SocketAddressV6_instCoeSocketAddress = (const lean_object*)&l_Std_Net_SocketAddressV6_instCoeSocketAddress___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Net_IPAddr_family(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_family___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_toString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_toString___boxed(lean_object*);
static const lean_closure_object l_Std_Net_IPAddr_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Net_IPAddr_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Net_IPAddr_instToString___closed__0 = (const lean_object*)&l_Std_Net_IPAddr_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Net_IPAddr_instToString = (const lean_object*)&l_Std_Net_IPAddr_instToString___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Net_SocketAddress_family(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_family___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ipAddr(lean_object*);
LEAN_EXPORT uint16_t l_Std_Net_SocketAddress_port(lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_port___boxed(lean_object*);
static const lean_string_object l_Std_Net_instInhabitedInterfaceAddress_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Net_instInhabitedInterfaceAddress_default___closed__0 = (const lean_object*)&l_Std_Net_instInhabitedInterfaceAddress_default___closed__0_value;
static lean_once_cell_t l_Std_Net_instInhabitedInterfaceAddress_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Net_instInhabitedInterfaceAddress_default___closed__1;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedInterfaceAddress_default;
LEAN_EXPORT lean_object* l_Std_Net_instInhabitedInterfaceAddress;
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqInterfaceAddress_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqInterfaceAddress_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqInterfaceAddress(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqInterfaceAddress___boxed(lean_object*, lean_object*);
lean_object* lean_uv_interface_addresses();
LEAN_EXPORT lean_object* l_Std_Net_interfaceAddresses___boxed(lean_object*);
static uint8_t _init_l_Std_Net_instInhabitedMACAddr_default___closed__0(void){
_start:
{
lean_object* v___x_1_; uint8_t v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_uint8_of_nat(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedMACAddr_default___closed__1(void){
_start:
{
uint8_t v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_3_ = lean_uint8_once(&l_Std_Net_instInhabitedMACAddr_default___closed__0, &l_Std_Net_instInhabitedMACAddr_default___closed__0_once, _init_l_Std_Net_instInhabitedMACAddr_default___closed__0);
v___x_4_ = lean_unsigned_to_nat(6u);
v___x_5_ = lean_box(v___x_3_);
v___x_6_ = lean_mk_array(v___x_4_, v___x_5_);
return v___x_6_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedMACAddr_default(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_once(&l_Std_Net_instInhabitedMACAddr_default___closed__1, &l_Std_Net_instInhabitedMACAddr_default___closed__1_once, _init_l_Std_Net_instInhabitedMACAddr_default___closed__1);
return v___x_7_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedMACAddr(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Std_Net_instInhabitedMACAddr_default;
return v___x_8_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqMACAddr_decEq(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = lean_alloc_closure((void*)(l_instDecidableEqUInt8___boxed), 2, 0);
v___x_12_ = l_Array_instDecidableEqImpl___redArg(v___x_11_, v_x_9_, v_x_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqMACAddr_decEq___boxed(lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Std_Net_instDecidableEqMACAddr_decEq(v_x_13_, v_x_14_);
lean_dec_ref(v_x_14_);
lean_dec_ref(v_x_13_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqMACAddr(lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
uint8_t v___x_19_; 
v___x_19_ = l_Std_Net_instDecidableEqMACAddr_decEq(v_x_17_, v_x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqMACAddr___boxed(lean_object* v_x_20_, lean_object* v_x_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = l_Std_Net_instDecidableEqMACAddr(v_x_20_, v_x_21_);
lean_dec_ref(v_x_21_);
lean_dec_ref(v_x_20_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPv4Addr_default___closed__0(void){
_start:
{
uint8_t v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_24_ = lean_uint8_once(&l_Std_Net_instInhabitedMACAddr_default___closed__0, &l_Std_Net_instInhabitedMACAddr_default___closed__0_once, _init_l_Std_Net_instInhabitedMACAddr_default___closed__0);
v___x_25_ = lean_unsigned_to_nat(4u);
v___x_26_ = lean_box(v___x_24_);
v___x_27_ = lean_mk_array(v___x_25_, v___x_26_);
return v___x_27_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPv4Addr_default(void){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_obj_once(&l_Std_Net_instInhabitedIPv4Addr_default___closed__0, &l_Std_Net_instInhabitedIPv4Addr_default___closed__0_once, _init_l_Std_Net_instInhabitedIPv4Addr_default___closed__0);
return v___x_28_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPv4Addr(void){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Std_Net_instInhabitedIPv4Addr_default;
return v___x_29_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPv4Addr_decEq(lean_object* v_x_30_, lean_object* v_x_31_){
_start:
{
lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_32_ = lean_alloc_closure((void*)(l_instDecidableEqUInt8___boxed), 2, 0);
v___x_33_ = l_Array_instDecidableEqImpl___redArg(v___x_32_, v_x_30_, v_x_31_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPv4Addr_decEq___boxed(lean_object* v_x_34_, lean_object* v_x_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_x_34_, v_x_35_);
lean_dec_ref(v_x_35_);
lean_dec_ref(v_x_34_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPv4Addr(lean_object* v_x_38_, lean_object* v_x_39_){
_start:
{
uint8_t v___x_40_; 
v___x_40_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_x_38_, v_x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPv4Addr___boxed(lean_object* v_x_41_, lean_object* v_x_42_){
_start:
{
uint8_t v_res_43_; lean_object* v_r_44_; 
v_res_43_ = l_Std_Net_instDecidableEqIPv4Addr(v_x_41_, v_x_42_);
lean_dec_ref(v_x_42_);
lean_dec_ref(v_x_41_);
v_r_44_ = lean_box(v_res_43_);
return v_r_44_;
}
}
static uint16_t _init_l_Std_Net_instInhabitedSocketAddressV4_default___closed__0(void){
_start:
{
lean_object* v___x_45_; uint16_t v___x_46_; 
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_uint16_of_nat(v___x_45_);
return v___x_46_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddressV4_default___closed__1(void){
_start:
{
uint16_t v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_47_ = lean_uint16_once(&l_Std_Net_instInhabitedSocketAddressV4_default___closed__0, &l_Std_Net_instInhabitedSocketAddressV4_default___closed__0_once, _init_l_Std_Net_instInhabitedSocketAddressV4_default___closed__0);
v___x_48_ = l_Std_Net_instInhabitedIPv4Addr_default;
v___x_49_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_49_, 0, v___x_48_);
lean_ctor_set_uint16(v___x_49_, sizeof(void*)*1, v___x_47_);
return v___x_49_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddressV4_default(void){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_obj_once(&l_Std_Net_instInhabitedSocketAddressV4_default___closed__1, &l_Std_Net_instInhabitedSocketAddressV4_default___closed__1_once, _init_l_Std_Net_instInhabitedSocketAddressV4_default___closed__1);
return v___x_50_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddressV4(void){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Std_Net_instInhabitedSocketAddressV4_default;
return v___x_51_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddressV4_decEq(lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
lean_object* v_addr_54_; uint16_t v_port_55_; lean_object* v_addr_56_; uint16_t v_port_57_; uint8_t v___x_58_; 
v_addr_54_ = lean_ctor_get(v_x_52_, 0);
v_port_55_ = lean_ctor_get_uint16(v_x_52_, sizeof(void*)*1);
v_addr_56_ = lean_ctor_get(v_x_53_, 0);
v_port_57_ = lean_ctor_get_uint16(v_x_53_, sizeof(void*)*1);
v___x_58_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_addr_54_, v_addr_56_);
if (v___x_58_ == 0)
{
return v___x_58_;
}
else
{
uint8_t v___x_59_; 
v___x_59_ = lean_uint16_dec_eq(v_port_55_, v_port_57_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddressV4_decEq___boxed(lean_object* v_x_60_, lean_object* v_x_61_){
_start:
{
uint8_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = l_Std_Net_instDecidableEqSocketAddressV4_decEq(v_x_60_, v_x_61_);
lean_dec_ref(v_x_61_);
lean_dec_ref(v_x_60_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddressV4(lean_object* v_x_64_, lean_object* v_x_65_){
_start:
{
uint8_t v___x_66_; 
v___x_66_ = l_Std_Net_instDecidableEqSocketAddressV4_decEq(v_x_64_, v_x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddressV4___boxed(lean_object* v_x_67_, lean_object* v_x_68_){
_start:
{
uint8_t v_res_69_; lean_object* v_r_70_; 
v_res_69_ = l_Std_Net_instDecidableEqSocketAddressV4(v_x_67_, v_x_68_);
lean_dec_ref(v_x_68_);
lean_dec_ref(v_x_67_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPv6Addr_default___closed__0(void){
_start:
{
uint16_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_71_ = lean_uint16_once(&l_Std_Net_instInhabitedSocketAddressV4_default___closed__0, &l_Std_Net_instInhabitedSocketAddressV4_default___closed__0_once, _init_l_Std_Net_instInhabitedSocketAddressV4_default___closed__0);
v___x_72_ = lean_unsigned_to_nat(8u);
v___x_73_ = lean_box(v___x_71_);
v___x_74_ = lean_mk_array(v___x_72_, v___x_73_);
return v___x_74_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPv6Addr_default(void){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_obj_once(&l_Std_Net_instInhabitedIPv6Addr_default___closed__0, &l_Std_Net_instInhabitedIPv6Addr_default___closed__0_once, _init_l_Std_Net_instInhabitedIPv6Addr_default___closed__0);
return v___x_75_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPv6Addr(void){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Std_Net_instInhabitedIPv6Addr_default;
return v___x_76_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPv6Addr_decEq(lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = lean_alloc_closure((void*)(l_instDecidableEqUInt16___boxed), 2, 0);
v___x_80_ = l_Array_instDecidableEqImpl___redArg(v___x_79_, v_x_77_, v_x_78_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPv6Addr_decEq___boxed(lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_x_81_, v_x_82_);
lean_dec_ref(v_x_82_);
lean_dec_ref(v_x_81_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPv6Addr(lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
uint8_t v___x_87_; 
v___x_87_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_x_85_, v_x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPv6Addr___boxed(lean_object* v_x_88_, lean_object* v_x_89_){
_start:
{
uint8_t v_res_90_; lean_object* v_r_91_; 
v_res_90_ = l_Std_Net_instDecidableEqIPv6Addr(v_x_88_, v_x_89_);
lean_dec_ref(v_x_89_);
lean_dec_ref(v_x_88_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddressV6_default___closed__0(void){
_start:
{
uint16_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = lean_uint16_once(&l_Std_Net_instInhabitedSocketAddressV4_default___closed__0, &l_Std_Net_instInhabitedSocketAddressV4_default___closed__0_once, _init_l_Std_Net_instInhabitedSocketAddressV4_default___closed__0);
v___x_93_ = l_Std_Net_instInhabitedIPv6Addr_default;
v___x_94_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set_uint16(v___x_94_, sizeof(void*)*1, v___x_92_);
return v___x_94_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddressV6_default(void){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_obj_once(&l_Std_Net_instInhabitedSocketAddressV6_default___closed__0, &l_Std_Net_instInhabitedSocketAddressV6_default___closed__0_once, _init_l_Std_Net_instInhabitedSocketAddressV6_default___closed__0);
return v___x_95_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddressV6(void){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Std_Net_instInhabitedSocketAddressV6_default;
return v___x_96_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddressV6_decEq(lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
lean_object* v_addr_99_; uint16_t v_port_100_; lean_object* v_addr_101_; uint16_t v_port_102_; uint8_t v___x_103_; 
v_addr_99_ = lean_ctor_get(v_x_97_, 0);
v_port_100_ = lean_ctor_get_uint16(v_x_97_, sizeof(void*)*1);
v_addr_101_ = lean_ctor_get(v_x_98_, 0);
v_port_102_ = lean_ctor_get_uint16(v_x_98_, sizeof(void*)*1);
v___x_103_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_addr_99_, v_addr_101_);
if (v___x_103_ == 0)
{
return v___x_103_;
}
else
{
uint8_t v___x_104_; 
v___x_104_ = lean_uint16_dec_eq(v_port_100_, v_port_102_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddressV6_decEq___boxed(lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
uint8_t v_res_107_; lean_object* v_r_108_; 
v_res_107_ = l_Std_Net_instDecidableEqSocketAddressV6_decEq(v_x_105_, v_x_106_);
lean_dec_ref(v_x_106_);
lean_dec_ref(v_x_105_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddressV6(lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
uint8_t v___x_111_; 
v___x_111_ = l_Std_Net_instDecidableEqSocketAddressV6_decEq(v_x_109_, v_x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddressV6___boxed(lean_object* v_x_112_, lean_object* v_x_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l_Std_Net_instDecidableEqSocketAddressV6(v_x_112_, v_x_113_);
lean_dec_ref(v_x_113_);
lean_dec_ref(v_x_112_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorIdx(lean_object* v_x_116_){
_start:
{
if (lean_obj_tag(v_x_116_) == 0)
{
lean_object* v___x_117_; 
v___x_117_ = lean_unsigned_to_nat(0u);
return v___x_117_;
}
else
{
lean_object* v___x_118_; 
v___x_118_ = lean_unsigned_to_nat(1u);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorIdx___boxed(lean_object* v_x_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Std_Net_IPAddr_ctorIdx(v_x_119_);
lean_dec_ref(v_x_119_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorElim___redArg(lean_object* v_t_121_, lean_object* v_k_122_){
_start:
{
lean_object* v_addr_123_; lean_object* v___x_124_; 
v_addr_123_ = lean_ctor_get(v_t_121_, 0);
lean_inc_ref(v_addr_123_);
lean_dec_ref(v_t_121_);
v___x_124_ = lean_apply_1(v_k_122_, v_addr_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorElim(lean_object* v_motive_125_, lean_object* v_ctorIdx_126_, lean_object* v_t_127_, lean_object* v_h_128_, lean_object* v_k_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_127_, v_k_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_ctorElim___boxed(lean_object* v_motive_131_, lean_object* v_ctorIdx_132_, lean_object* v_t_133_, lean_object* v_h_134_, lean_object* v_k_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Std_Net_IPAddr_ctorElim(v_motive_131_, v_ctorIdx_132_, v_t_133_, v_h_134_, v_k_135_);
lean_dec(v_ctorIdx_132_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v4_elim___redArg(lean_object* v_t_137_, lean_object* v_v4_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_137_, v_v4_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v4_elim(lean_object* v_motive_140_, lean_object* v_t_141_, lean_object* v_h_142_, lean_object* v_v4_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_141_, v_v4_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v6_elim___redArg(lean_object* v_t_145_, lean_object* v_v6_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_145_, v_v6_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_v6_elim(lean_object* v_motive_148_, lean_object* v_t_149_, lean_object* v_h_150_, lean_object* v_v6_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Std_Net_IPAddr_ctorElim___redArg(v_t_149_, v_v6_151_);
return v___x_152_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPAddr_default___closed__0(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = l_Std_Net_instInhabitedIPv4Addr_default;
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPAddr_default(void){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = lean_obj_once(&l_Std_Net_instInhabitedIPAddr_default___closed__0, &l_Std_Net_instInhabitedIPAddr_default___closed__0_once, _init_l_Std_Net_instInhabitedIPAddr_default___closed__0);
return v___x_155_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedIPAddr(void){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Std_Net_instInhabitedIPAddr_default;
return v___x_156_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPAddr_decEq(lean_object* v_x_157_, lean_object* v_x_158_){
_start:
{
if (lean_obj_tag(v_x_157_) == 0)
{
if (lean_obj_tag(v_x_158_) == 0)
{
lean_object* v_addr_159_; lean_object* v_addr_160_; uint8_t v___x_161_; 
v_addr_159_ = lean_ctor_get(v_x_157_, 0);
v_addr_160_ = lean_ctor_get(v_x_158_, 0);
v___x_161_ = l_Std_Net_instDecidableEqIPv4Addr_decEq(v_addr_159_, v_addr_160_);
return v___x_161_;
}
else
{
uint8_t v___x_162_; 
v___x_162_ = 0;
return v___x_162_;
}
}
else
{
if (lean_obj_tag(v_x_158_) == 0)
{
uint8_t v___x_163_; 
v___x_163_ = 0;
return v___x_163_;
}
else
{
lean_object* v_addr_164_; lean_object* v_addr_165_; uint8_t v___x_166_; 
v_addr_164_ = lean_ctor_get(v_x_157_, 0);
v_addr_165_ = lean_ctor_get(v_x_158_, 0);
v___x_166_ = l_Std_Net_instDecidableEqIPv6Addr_decEq(v_addr_164_, v_addr_165_);
return v___x_166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPAddr_decEq___boxed(lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_Std_Net_instDecidableEqIPAddr_decEq(v_x_167_, v_x_168_);
lean_dec_ref(v_x_168_);
lean_dec_ref(v_x_167_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqIPAddr(lean_object* v_x_171_, lean_object* v_x_172_){
_start:
{
uint8_t v___x_173_; 
v___x_173_ = l_Std_Net_instDecidableEqIPAddr_decEq(v_x_171_, v_x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqIPAddr___boxed(lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
uint8_t v_res_176_; lean_object* v_r_177_; 
v_res_176_ = l_Std_Net_instDecidableEqIPAddr(v_x_174_, v_x_175_);
lean_dec_ref(v_x_175_);
lean_dec_ref(v_x_174_);
v_r_177_ = lean_box(v_res_176_);
return v_r_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorIdx(lean_object* v_x_178_){
_start:
{
if (lean_obj_tag(v_x_178_) == 0)
{
lean_object* v___x_179_; 
v___x_179_ = lean_unsigned_to_nat(0u);
return v___x_179_;
}
else
{
lean_object* v___x_180_; 
v___x_180_ = lean_unsigned_to_nat(1u);
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorIdx___boxed(lean_object* v_x_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Std_Net_SocketAddress_ctorIdx(v_x_181_);
lean_dec_ref(v_x_181_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorElim___redArg(lean_object* v_t_183_, lean_object* v_k_184_){
_start:
{
lean_object* v_addr_185_; lean_object* v___x_186_; 
v_addr_185_ = lean_ctor_get(v_t_183_, 0);
lean_inc_ref(v_addr_185_);
lean_dec_ref(v_t_183_);
v___x_186_ = lean_apply_1(v_k_184_, v_addr_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorElim(lean_object* v_motive_187_, lean_object* v_ctorIdx_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_k_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_189_, v_k_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ctorElim___boxed(lean_object* v_motive_193_, lean_object* v_ctorIdx_194_, lean_object* v_t_195_, lean_object* v_h_196_, lean_object* v_k_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Std_Net_SocketAddress_ctorElim(v_motive_193_, v_ctorIdx_194_, v_t_195_, v_h_196_, v_k_197_);
lean_dec(v_ctorIdx_194_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v4_elim___redArg(lean_object* v_t_199_, lean_object* v_v4_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_199_, v_v4_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v4_elim(lean_object* v_motive_202_, lean_object* v_t_203_, lean_object* v_h_204_, lean_object* v_v4_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_203_, v_v4_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v6_elim___redArg(lean_object* v_t_207_, lean_object* v_v6_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_207_, v_v6_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_v6_elim(lean_object* v_motive_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_v6_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Std_Net_SocketAddress_ctorElim___redArg(v_t_211_, v_v6_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddress_default___closed__0(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = l_Std_Net_instInhabitedSocketAddressV4_default;
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddress_default(void){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lean_obj_once(&l_Std_Net_instInhabitedSocketAddress_default___closed__0, &l_Std_Net_instInhabitedSocketAddress_default___closed__0_once, _init_l_Std_Net_instInhabitedSocketAddress_default___closed__0);
return v___x_217_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedSocketAddress(void){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Std_Net_instInhabitedSocketAddress_default;
return v___x_218_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddress_decEq(lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
if (lean_obj_tag(v_x_219_) == 0)
{
if (lean_obj_tag(v_x_220_) == 0)
{
lean_object* v_addr_221_; lean_object* v_addr_222_; uint8_t v___x_223_; 
v_addr_221_ = lean_ctor_get(v_x_219_, 0);
v_addr_222_ = lean_ctor_get(v_x_220_, 0);
v___x_223_ = l_Std_Net_instDecidableEqSocketAddressV4_decEq(v_addr_221_, v_addr_222_);
return v___x_223_;
}
else
{
uint8_t v___x_224_; 
v___x_224_ = 0;
return v___x_224_;
}
}
else
{
if (lean_obj_tag(v_x_220_) == 0)
{
uint8_t v___x_225_; 
v___x_225_ = 0;
return v___x_225_;
}
else
{
lean_object* v_addr_226_; lean_object* v_addr_227_; uint8_t v___x_228_; 
v_addr_226_ = lean_ctor_get(v_x_219_, 0);
v_addr_227_ = lean_ctor_get(v_x_220_, 0);
v___x_228_ = l_Std_Net_instDecidableEqSocketAddressV6_decEq(v_addr_226_, v_addr_227_);
return v___x_228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddress_decEq___boxed(lean_object* v_x_229_, lean_object* v_x_230_){
_start:
{
uint8_t v_res_231_; lean_object* v_r_232_; 
v_res_231_ = l_Std_Net_instDecidableEqSocketAddress_decEq(v_x_229_, v_x_230_);
lean_dec_ref(v_x_230_);
lean_dec_ref(v_x_229_);
v_r_232_ = lean_box(v_res_231_);
return v_r_232_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqSocketAddress(lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
uint8_t v___x_235_; 
v___x_235_ = l_Std_Net_instDecidableEqSocketAddress_decEq(v_x_233_, v_x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqSocketAddress___boxed(lean_object* v_x_236_, lean_object* v_x_237_){
_start:
{
uint8_t v_res_238_; lean_object* v_r_239_; 
v_res_238_ = l_Std_Net_instDecidableEqSocketAddress(v_x_236_, v_x_237_);
lean_dec_ref(v_x_237_);
lean_dec_ref(v_x_236_);
v_r_239_ = lean_box(v_res_238_);
return v_r_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorIdx(uint8_t v_x_240_){
_start:
{
if (v_x_240_ == 0)
{
lean_object* v___x_241_; 
v___x_241_ = lean_unsigned_to_nat(0u);
return v___x_241_;
}
else
{
lean_object* v___x_242_; 
v___x_242_ = lean_unsigned_to_nat(1u);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorIdx___boxed(lean_object* v_x_243_){
_start:
{
uint8_t v_x_boxed_244_; lean_object* v_res_245_; 
v_x_boxed_244_ = lean_unbox(v_x_243_);
v_res_245_ = l_Std_Net_AddressFamily_ctorIdx(v_x_boxed_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_toCtorIdx(uint8_t v_x_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Std_Net_AddressFamily_ctorIdx(v_x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_toCtorIdx___boxed(lean_object* v_x_248_){
_start:
{
uint8_t v_x_4__boxed_249_; lean_object* v_res_250_; 
v_x_4__boxed_249_ = lean_unbox(v_x_248_);
v_res_250_ = l_Std_Net_AddressFamily_toCtorIdx(v_x_4__boxed_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim___redArg(lean_object* v_k_251_){
_start:
{
lean_inc(v_k_251_);
return v_k_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim___redArg___boxed(lean_object* v_k_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Std_Net_AddressFamily_ctorElim___redArg(v_k_252_);
lean_dec(v_k_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim(lean_object* v_motive_254_, lean_object* v_ctorIdx_255_, uint8_t v_t_256_, lean_object* v_h_257_, lean_object* v_k_258_){
_start:
{
lean_inc(v_k_258_);
return v_k_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ctorElim___boxed(lean_object* v_motive_259_, lean_object* v_ctorIdx_260_, lean_object* v_t_261_, lean_object* v_h_262_, lean_object* v_k_263_){
_start:
{
uint8_t v_t_boxed_264_; lean_object* v_res_265_; 
v_t_boxed_264_ = lean_unbox(v_t_261_);
v_res_265_ = l_Std_Net_AddressFamily_ctorElim(v_motive_259_, v_ctorIdx_260_, v_t_boxed_264_, v_h_262_, v_k_263_);
lean_dec(v_k_263_);
lean_dec(v_ctorIdx_260_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim___redArg(lean_object* v_ipv4_266_){
_start:
{
lean_inc(v_ipv4_266_);
return v_ipv4_266_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim___redArg___boxed(lean_object* v_ipv4_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Std_Net_AddressFamily_ipv4_elim___redArg(v_ipv4_267_);
lean_dec(v_ipv4_267_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim(lean_object* v_motive_269_, uint8_t v_t_270_, lean_object* v_h_271_, lean_object* v_ipv4_272_){
_start:
{
lean_inc(v_ipv4_272_);
return v_ipv4_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv4_elim___boxed(lean_object* v_motive_273_, lean_object* v_t_274_, lean_object* v_h_275_, lean_object* v_ipv4_276_){
_start:
{
uint8_t v_t_boxed_277_; lean_object* v_res_278_; 
v_t_boxed_277_ = lean_unbox(v_t_274_);
v_res_278_ = l_Std_Net_AddressFamily_ipv4_elim(v_motive_273_, v_t_boxed_277_, v_h_275_, v_ipv4_276_);
lean_dec(v_ipv4_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim___redArg(lean_object* v_ipv6_279_){
_start:
{
lean_inc(v_ipv6_279_);
return v_ipv6_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim___redArg___boxed(lean_object* v_ipv6_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Std_Net_AddressFamily_ipv6_elim___redArg(v_ipv6_280_);
lean_dec(v_ipv6_280_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim(lean_object* v_motive_282_, uint8_t v_t_283_, lean_object* v_h_284_, lean_object* v_ipv6_285_){
_start:
{
lean_inc(v_ipv6_285_);
return v_ipv6_285_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ipv6_elim___boxed(lean_object* v_motive_286_, lean_object* v_t_287_, lean_object* v_h_288_, lean_object* v_ipv6_289_){
_start:
{
uint8_t v_t_boxed_290_; lean_object* v_res_291_; 
v_t_boxed_290_ = lean_unbox(v_t_287_);
v_res_291_ = l_Std_Net_AddressFamily_ipv6_elim(v_motive_286_, v_t_boxed_290_, v_h_288_, v_ipv6_289_);
lean_dec(v_ipv6_289_);
return v_res_291_;
}
}
static uint8_t _init_l_Std_Net_instInhabitedAddressFamily_default(void){
_start:
{
uint8_t v___x_292_; 
v___x_292_ = 0;
return v___x_292_;
}
}
static uint8_t _init_l_Std_Net_instInhabitedAddressFamily(void){
_start:
{
uint8_t v___x_293_; 
v___x_293_ = 0;
return v___x_293_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_AddressFamily_ofNat(lean_object* v_n_294_){
_start:
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = lean_unsigned_to_nat(0u);
v___x_296_ = lean_nat_dec_le(v_n_294_, v___x_295_);
if (v___x_296_ == 0)
{
uint8_t v___x_297_; 
v___x_297_ = 1;
return v___x_297_;
}
else
{
uint8_t v___x_298_; 
v___x_298_ = 0;
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_AddressFamily_ofNat___boxed(lean_object* v_n_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l_Std_Net_AddressFamily_ofNat(v_n_299_);
lean_dec(v_n_299_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqAddressFamily(uint8_t v_x_302_, uint8_t v_y_303_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_304_ = l_Std_Net_AddressFamily_ctorIdx(v_x_302_);
v___x_305_ = l_Std_Net_AddressFamily_ctorIdx(v_y_303_);
v___x_306_ = lean_nat_dec_eq(v___x_304_, v___x_305_);
lean_dec(v___x_305_);
lean_dec(v___x_304_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqAddressFamily___boxed(lean_object* v_x_307_, lean_object* v_y_308_){
_start:
{
uint8_t v_x_13__boxed_309_; uint8_t v_y_14__boxed_310_; uint8_t v_res_311_; lean_object* v_r_312_; 
v_x_13__boxed_309_ = lean_unbox(v_x_307_);
v_y_14__boxed_310_ = lean_unbox(v_y_308_);
v_res_311_ = l_Std_Net_instDecidableEqAddressFamily(v_x_13__boxed_309_, v_y_14__boxed_310_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_ofParts(uint8_t v_a_313_, uint8_t v_b_314_, uint8_t v_c_315_, uint8_t v_d_316_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_317_ = lean_unsigned_to_nat(4u);
v___x_318_ = lean_mk_empty_array_with_capacity(v___x_317_);
v___x_319_ = lean_box(v_a_313_);
v___x_320_ = lean_array_push(v___x_318_, v___x_319_);
v___x_321_ = lean_box(v_b_314_);
v___x_322_ = lean_array_push(v___x_320_, v___x_321_);
v___x_323_ = lean_box(v_c_315_);
v___x_324_ = lean_array_push(v___x_322_, v___x_323_);
v___x_325_ = lean_box(v_d_316_);
v___x_326_ = lean_array_push(v___x_324_, v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_ofParts___boxed(lean_object* v_a_327_, lean_object* v_b_328_, lean_object* v_c_329_, lean_object* v_d_330_){
_start:
{
uint8_t v_a_boxed_331_; uint8_t v_b_boxed_332_; uint8_t v_c_boxed_333_; uint8_t v_d_boxed_334_; lean_object* v_res_335_; 
v_a_boxed_331_ = lean_unbox(v_a_327_);
v_b_boxed_332_ = lean_unbox(v_b_328_);
v_c_boxed_333_ = lean_unbox(v_c_329_);
v_d_boxed_334_ = lean_unbox(v_d_330_);
v_res_335_ = l_Std_Net_IPv4Addr_ofParts(v_a_boxed_331_, v_b_boxed_332_, v_c_boxed_333_, v_d_boxed_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_ofString___boxed(lean_object* v_s_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = lean_uv_pton_v4(v_s_337_);
lean_dec_ref(v_s_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_toString___boxed(lean_object* v_addr_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = lean_uv_ntop_v4(v_addr_340_);
lean_dec_ref(v_addr_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv4Addr_instCoeIPAddr___lam__0(lean_object* v_addr_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v_addr_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV4_instCoeSocketAddress___lam__0(lean_object* v_addr_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_349_, 0, v_addr_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_ofParts(uint16_t v_a_352_, uint16_t v_b_353_, uint16_t v_c_354_, uint16_t v_d_355_, uint16_t v_e_356_, uint16_t v_f_357_, uint16_t v_g_358_, uint16_t v_h_359_){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_360_ = lean_unsigned_to_nat(8u);
v___x_361_ = lean_mk_empty_array_with_capacity(v___x_360_);
v___x_362_ = lean_box(v_a_352_);
v___x_363_ = lean_array_push(v___x_361_, v___x_362_);
v___x_364_ = lean_box(v_b_353_);
v___x_365_ = lean_array_push(v___x_363_, v___x_364_);
v___x_366_ = lean_box(v_c_354_);
v___x_367_ = lean_array_push(v___x_365_, v___x_366_);
v___x_368_ = lean_box(v_d_355_);
v___x_369_ = lean_array_push(v___x_367_, v___x_368_);
v___x_370_ = lean_box(v_e_356_);
v___x_371_ = lean_array_push(v___x_369_, v___x_370_);
v___x_372_ = lean_box(v_f_357_);
v___x_373_ = lean_array_push(v___x_371_, v___x_372_);
v___x_374_ = lean_box(v_g_358_);
v___x_375_ = lean_array_push(v___x_373_, v___x_374_);
v___x_376_ = lean_box(v_h_359_);
v___x_377_ = lean_array_push(v___x_375_, v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_ofParts___boxed(lean_object* v_a_378_, lean_object* v_b_379_, lean_object* v_c_380_, lean_object* v_d_381_, lean_object* v_e_382_, lean_object* v_f_383_, lean_object* v_g_384_, lean_object* v_h_385_){
_start:
{
uint16_t v_a_boxed_386_; uint16_t v_b_boxed_387_; uint16_t v_c_boxed_388_; uint16_t v_d_boxed_389_; uint16_t v_e_boxed_390_; uint16_t v_f_boxed_391_; uint16_t v_g_boxed_392_; uint16_t v_h_boxed_393_; lean_object* v_res_394_; 
v_a_boxed_386_ = lean_unbox(v_a_378_);
v_b_boxed_387_ = lean_unbox(v_b_379_);
v_c_boxed_388_ = lean_unbox(v_c_380_);
v_d_boxed_389_ = lean_unbox(v_d_381_);
v_e_boxed_390_ = lean_unbox(v_e_382_);
v_f_boxed_391_ = lean_unbox(v_f_383_);
v_g_boxed_392_ = lean_unbox(v_g_384_);
v_h_boxed_393_ = lean_unbox(v_h_385_);
v_res_394_ = l_Std_Net_IPv6Addr_ofParts(v_a_boxed_386_, v_b_boxed_387_, v_c_boxed_388_, v_d_boxed_389_, v_e_boxed_390_, v_f_boxed_391_, v_g_boxed_392_, v_h_boxed_393_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_ofString___boxed(lean_object* v_s_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = lean_uv_pton_v6(v_s_396_);
lean_dec_ref(v_s_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_toString___boxed(lean_object* v_addr_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = lean_uv_ntop_v6(v_addr_399_);
lean_dec_ref(v_addr_399_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPv6Addr_instCoeIPAddr___lam__0(lean_object* v_addr_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_404_, 0, v_addr_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddressV6_instCoeSocketAddress___lam__0(lean_object* v_addr_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_408_, 0, v_addr_407_);
return v___x_408_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_IPAddr_family(lean_object* v_x_411_){
_start:
{
if (lean_obj_tag(v_x_411_) == 0)
{
uint8_t v___x_412_; 
v___x_412_ = 0;
return v___x_412_;
}
else
{
uint8_t v___x_413_; 
v___x_413_ = 1;
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_family___boxed(lean_object* v_x_414_){
_start:
{
uint8_t v_res_415_; lean_object* v_r_416_; 
v_res_415_ = l_Std_Net_IPAddr_family(v_x_414_);
lean_dec_ref(v_x_414_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_toString(lean_object* v_x_417_){
_start:
{
if (lean_obj_tag(v_x_417_) == 0)
{
lean_object* v_addr_418_; lean_object* v___x_419_; 
v_addr_418_ = lean_ctor_get(v_x_417_, 0);
v___x_419_ = lean_uv_ntop_v4(v_addr_418_);
return v___x_419_;
}
else
{
lean_object* v_addr_420_; lean_object* v___x_421_; 
v_addr_420_ = lean_ctor_get(v_x_417_, 0);
v___x_421_ = lean_uv_ntop_v6(v_addr_420_);
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_IPAddr_toString___boxed(lean_object* v_x_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Std_Net_IPAddr_toString(v_x_422_);
lean_dec_ref(v_x_422_);
return v_res_423_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_SocketAddress_family(lean_object* v_x_426_){
_start:
{
if (lean_obj_tag(v_x_426_) == 0)
{
uint8_t v___x_427_; 
v___x_427_ = 0;
return v___x_427_;
}
else
{
uint8_t v___x_428_; 
v___x_428_ = 1;
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_family___boxed(lean_object* v_x_429_){
_start:
{
uint8_t v_res_430_; lean_object* v_r_431_; 
v_res_430_ = l_Std_Net_SocketAddress_family(v_x_429_);
lean_dec_ref(v_x_429_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_ipAddr(lean_object* v_x_432_){
_start:
{
if (lean_obj_tag(v_x_432_) == 0)
{
lean_object* v_addr_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_441_; 
v_addr_433_ = lean_ctor_get(v_x_432_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v_x_432_);
if (v_isSharedCheck_441_ == 0)
{
v___x_435_ = v_x_432_;
v_isShared_436_ = v_isSharedCheck_441_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_addr_433_);
lean_dec(v_x_432_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_441_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v_addr_437_; lean_object* v___x_439_; 
v_addr_437_ = lean_ctor_get(v_addr_433_, 0);
lean_inc_ref(v_addr_437_);
lean_dec_ref(v_addr_433_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v_addr_437_);
v___x_439_ = v___x_435_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_addr_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
else
{
lean_object* v_addr_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_450_; 
v_addr_442_ = lean_ctor_get(v_x_432_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v_x_432_);
if (v_isSharedCheck_450_ == 0)
{
v___x_444_ = v_x_432_;
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_addr_442_);
lean_dec(v_x_432_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_450_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v_addr_446_; lean_object* v___x_448_; 
v_addr_446_ = lean_ctor_get(v_addr_442_, 0);
lean_inc_ref(v_addr_446_);
lean_dec_ref(v_addr_442_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v_addr_446_);
v___x_448_ = v___x_444_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_addr_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
}
LEAN_EXPORT uint16_t l_Std_Net_SocketAddress_port(lean_object* v_x_451_){
_start:
{
lean_object* v_addr_452_; uint16_t v_port_453_; 
v_addr_452_ = lean_ctor_get(v_x_451_, 0);
v_port_453_ = lean_ctor_get_uint16(v_addr_452_, sizeof(void*)*1);
return v_port_453_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_SocketAddress_port___boxed(lean_object* v_x_454_){
_start:
{
uint16_t v_res_455_; lean_object* v_r_456_; 
v_res_455_ = l_Std_Net_SocketAddress_port(v_x_454_);
lean_dec_ref(v_x_454_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedInterfaceAddress_default___closed__1(void){
_start:
{
lean_object* v___x_458_; uint8_t v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_458_ = l_Std_Net_instInhabitedIPAddr_default;
v___x_459_ = 0;
v___x_460_ = l_Std_Net_instInhabitedMACAddr_default;
v___x_461_ = ((lean_object*)(l_Std_Net_instInhabitedInterfaceAddress_default___closed__0));
v___x_462_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___x_460_);
lean_ctor_set(v___x_462_, 2, v___x_458_);
lean_ctor_set(v___x_462_, 3, v___x_458_);
lean_ctor_set_uint8(v___x_462_, sizeof(void*)*4, v___x_459_);
return v___x_462_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedInterfaceAddress_default(void){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = lean_obj_once(&l_Std_Net_instInhabitedInterfaceAddress_default___closed__1, &l_Std_Net_instInhabitedInterfaceAddress_default___closed__1_once, _init_l_Std_Net_instInhabitedInterfaceAddress_default___closed__1);
return v___x_463_;
}
}
static lean_object* _init_l_Std_Net_instInhabitedInterfaceAddress(void){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Std_Net_instInhabitedInterfaceAddress_default;
return v___x_464_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqInterfaceAddress_decEq(lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
lean_object* v_name_467_; lean_object* v_physicalAddress_468_; uint8_t v_isLoopback_469_; lean_object* v_address_470_; lean_object* v_netMask_471_; lean_object* v_name_472_; lean_object* v_physicalAddress_473_; uint8_t v_isLoopback_474_; lean_object* v_address_475_; lean_object* v_netMask_476_; uint8_t v___x_480_; 
v_name_467_ = lean_ctor_get(v_x_465_, 0);
v_physicalAddress_468_ = lean_ctor_get(v_x_465_, 1);
v_isLoopback_469_ = lean_ctor_get_uint8(v_x_465_, sizeof(void*)*4);
v_address_470_ = lean_ctor_get(v_x_465_, 2);
v_netMask_471_ = lean_ctor_get(v_x_465_, 3);
v_name_472_ = lean_ctor_get(v_x_466_, 0);
v_physicalAddress_473_ = lean_ctor_get(v_x_466_, 1);
v_isLoopback_474_ = lean_ctor_get_uint8(v_x_466_, sizeof(void*)*4);
v_address_475_ = lean_ctor_get(v_x_466_, 2);
v_netMask_476_ = lean_ctor_get(v_x_466_, 3);
v___x_480_ = lean_string_dec_eq(v_name_467_, v_name_472_);
if (v___x_480_ == 0)
{
return v___x_480_;
}
else
{
uint8_t v___x_481_; 
v___x_481_ = l_Std_Net_instDecidableEqMACAddr_decEq(v_physicalAddress_468_, v_physicalAddress_473_);
if (v___x_481_ == 0)
{
return v___x_481_;
}
else
{
if (v_isLoopback_469_ == 0)
{
if (v_isLoopback_474_ == 0)
{
goto v___jp_477_;
}
else
{
return v_isLoopback_469_;
}
}
else
{
if (v_isLoopback_474_ == 0)
{
return v_isLoopback_474_;
}
else
{
goto v___jp_477_;
}
}
}
}
v___jp_477_:
{
uint8_t v___x_478_; 
v___x_478_ = l_Std_Net_instDecidableEqIPAddr_decEq(v_address_470_, v_address_475_);
if (v___x_478_ == 0)
{
return v___x_478_;
}
else
{
uint8_t v___x_479_; 
v___x_479_ = l_Std_Net_instDecidableEqIPAddr_decEq(v_netMask_471_, v_netMask_476_);
return v___x_479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqInterfaceAddress_decEq___boxed(lean_object* v_x_482_, lean_object* v_x_483_){
_start:
{
uint8_t v_res_484_; lean_object* v_r_485_; 
v_res_484_ = l_Std_Net_instDecidableEqInterfaceAddress_decEq(v_x_482_, v_x_483_);
lean_dec_ref(v_x_483_);
lean_dec_ref(v_x_482_);
v_r_485_ = lean_box(v_res_484_);
return v_r_485_;
}
}
LEAN_EXPORT uint8_t l_Std_Net_instDecidableEqInterfaceAddress(lean_object* v_x_486_, lean_object* v_x_487_){
_start:
{
uint8_t v___x_488_; 
v___x_488_ = l_Std_Net_instDecidableEqInterfaceAddress_decEq(v_x_486_, v_x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_instDecidableEqInterfaceAddress___boxed(lean_object* v_x_489_, lean_object* v_x_490_){
_start:
{
uint8_t v_res_491_; lean_object* v_r_492_; 
v_res_491_ = l_Std_Net_instDecidableEqInterfaceAddress(v_x_489_, v_x_490_);
lean_dec_ref(v_x_490_);
lean_dec_ref(v_x_489_);
v_r_492_ = lean_box(v_res_491_);
return v_r_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Net_interfaceAddresses___boxed(lean_object* v_a_00___x40___internal___hyg_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = lean_uv_interface_addresses();
return v_res_495_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Net_Addr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Net_instInhabitedMACAddr_default = _init_l_Std_Net_instInhabitedMACAddr_default();
lean_mark_persistent(l_Std_Net_instInhabitedMACAddr_default);
l_Std_Net_instInhabitedMACAddr = _init_l_Std_Net_instInhabitedMACAddr();
lean_mark_persistent(l_Std_Net_instInhabitedMACAddr);
l_Std_Net_instInhabitedIPv4Addr_default = _init_l_Std_Net_instInhabitedIPv4Addr_default();
lean_mark_persistent(l_Std_Net_instInhabitedIPv4Addr_default);
l_Std_Net_instInhabitedIPv4Addr = _init_l_Std_Net_instInhabitedIPv4Addr();
lean_mark_persistent(l_Std_Net_instInhabitedIPv4Addr);
l_Std_Net_instInhabitedSocketAddressV4_default = _init_l_Std_Net_instInhabitedSocketAddressV4_default();
lean_mark_persistent(l_Std_Net_instInhabitedSocketAddressV4_default);
l_Std_Net_instInhabitedSocketAddressV4 = _init_l_Std_Net_instInhabitedSocketAddressV4();
lean_mark_persistent(l_Std_Net_instInhabitedSocketAddressV4);
l_Std_Net_instInhabitedIPv6Addr_default = _init_l_Std_Net_instInhabitedIPv6Addr_default();
lean_mark_persistent(l_Std_Net_instInhabitedIPv6Addr_default);
l_Std_Net_instInhabitedIPv6Addr = _init_l_Std_Net_instInhabitedIPv6Addr();
lean_mark_persistent(l_Std_Net_instInhabitedIPv6Addr);
l_Std_Net_instInhabitedSocketAddressV6_default = _init_l_Std_Net_instInhabitedSocketAddressV6_default();
lean_mark_persistent(l_Std_Net_instInhabitedSocketAddressV6_default);
l_Std_Net_instInhabitedSocketAddressV6 = _init_l_Std_Net_instInhabitedSocketAddressV6();
lean_mark_persistent(l_Std_Net_instInhabitedSocketAddressV6);
l_Std_Net_instInhabitedIPAddr_default = _init_l_Std_Net_instInhabitedIPAddr_default();
lean_mark_persistent(l_Std_Net_instInhabitedIPAddr_default);
l_Std_Net_instInhabitedIPAddr = _init_l_Std_Net_instInhabitedIPAddr();
lean_mark_persistent(l_Std_Net_instInhabitedIPAddr);
l_Std_Net_instInhabitedSocketAddress_default = _init_l_Std_Net_instInhabitedSocketAddress_default();
lean_mark_persistent(l_Std_Net_instInhabitedSocketAddress_default);
l_Std_Net_instInhabitedSocketAddress = _init_l_Std_Net_instInhabitedSocketAddress();
lean_mark_persistent(l_Std_Net_instInhabitedSocketAddress);
l_Std_Net_instInhabitedAddressFamily_default = _init_l_Std_Net_instInhabitedAddressFamily_default();
l_Std_Net_instInhabitedAddressFamily = _init_l_Std_Net_instInhabitedAddressFamily();
l_Std_Net_instInhabitedInterfaceAddress_default = _init_l_Std_Net_instInhabitedInterfaceAddress_default();
lean_mark_persistent(l_Std_Net_instInhabitedInterfaceAddress_default);
l_Std_Net_instInhabitedInterfaceAddress = _init_l_Std_Net_instInhabitedInterfaceAddress();
lean_mark_persistent(l_Std_Net_instInhabitedInterfaceAddress);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Net_Addr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Net_Addr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Net_Addr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Net_Addr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Net_Addr(builtin);
}
#ifdef __cplusplus
}
#endif
