// Lean compiler output
// Module: Init.Data.Hashable
// Imports: import Init.Data.Array.Basic public import Init.Data.UInt.Basic
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
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_UInt32_toUInt64___boxed(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_UInt16_toUInt64___boxed(lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_USize_toUInt64___boxed(lean_object*);
lean_object* l_UInt8_toUInt64___boxed(lean_object*);
static const lean_closure_object l_instHashableNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableNat___closed__0 = (const lean_object*)&l_instHashableNat___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableNat = (const lean_object*)&l_instHashableNat___closed__0_value;
LEAN_EXPORT uint64_t l_instHashableProd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_instHashableBool___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_instHashableBool___lam__0___boxed(lean_object*);
static const lean_closure_object l_instHashableBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableBool___closed__0 = (const lean_object*)&l_instHashableBool___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableBool = (const lean_object*)&l_instHashableBool___closed__0_value;
LEAN_EXPORT uint64_t l_instHashablePEmpty___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_instHashablePEmpty___lam__0___boxed(lean_object*);
static const lean_closure_object l_instHashablePEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashablePEmpty___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashablePEmpty___closed__0 = (const lean_object*)&l_instHashablePEmpty___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashablePEmpty = (const lean_object*)&l_instHashablePEmpty___closed__0_value;
LEAN_EXPORT uint64_t l_instHashablePUnit___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instHashablePUnit___lam__0___boxed(lean_object*);
static const lean_closure_object l_instHashablePUnit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashablePUnit___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashablePUnit___closed__0 = (const lean_object*)&l_instHashablePUnit___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashablePUnit = (const lean_object*)&l_instHashablePUnit___closed__0_value;
LEAN_EXPORT uint64_t l_instHashableOption___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableOption___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instHashableOption(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_instHashableList___redArg___lam__0(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_instHashableList___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_instHashableList___redArg___lam__1___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(7, 0, 0, 0, 0, 0, 0, 0)}};
LEAN_EXPORT const lean_object* l_instHashableList___redArg___lam__1___boxed__const__1 = (const lean_object*)&l_instHashableList___redArg___lam__1___boxed__const__1_value;
LEAN_EXPORT uint64_t l_instHashableList___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableList___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instHashableList(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_instHashableArray___redArg___lam__0(lean_object*, uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_instHashableArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instHashableArray___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableArray___redArg___lam__1___closed__0 = (const lean_object*)&l_instHashableArray___redArg___lam__1___closed__0_value;
static const lean_closure_object l_instHashableArray___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableArray___redArg___lam__1___closed__1 = (const lean_object*)&l_instHashableArray___redArg___lam__1___closed__1_value;
static const lean_closure_object l_instHashableArray___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableArray___redArg___lam__1___closed__2 = (const lean_object*)&l_instHashableArray___redArg___lam__1___closed__2_value;
static const lean_closure_object l_instHashableArray___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableArray___redArg___lam__1___closed__3 = (const lean_object*)&l_instHashableArray___redArg___lam__1___closed__3_value;
static const lean_closure_object l_instHashableArray___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableArray___redArg___lam__1___closed__4 = (const lean_object*)&l_instHashableArray___redArg___lam__1___closed__4_value;
static const lean_closure_object l_instHashableArray___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableArray___redArg___lam__1___closed__5 = (const lean_object*)&l_instHashableArray___redArg___lam__1___closed__5_value;
static const lean_closure_object l_instHashableArray___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableArray___redArg___lam__1___closed__6 = (const lean_object*)&l_instHashableArray___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_instHashableArray___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instHashableArray___redArg___lam__1___closed__0_value),((lean_object*)&l_instHashableArray___redArg___lam__1___closed__1_value)}};
static const lean_object* l_instHashableArray___redArg___lam__1___closed__7 = (const lean_object*)&l_instHashableArray___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_instHashableArray___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_instHashableArray___redArg___lam__1___closed__7_value),((lean_object*)&l_instHashableArray___redArg___lam__1___closed__2_value),((lean_object*)&l_instHashableArray___redArg___lam__1___closed__3_value),((lean_object*)&l_instHashableArray___redArg___lam__1___closed__4_value),((lean_object*)&l_instHashableArray___redArg___lam__1___closed__5_value)}};
static const lean_object* l_instHashableArray___redArg___lam__1___closed__8 = (const lean_object*)&l_instHashableArray___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_instHashableArray___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_instHashableArray___redArg___lam__1___closed__8_value),((lean_object*)&l_instHashableArray___redArg___lam__1___closed__6_value)}};
static const lean_object* l_instHashableArray___redArg___lam__1___closed__9 = (const lean_object*)&l_instHashableArray___redArg___lam__1___closed__9_value;
LEAN_EXPORT uint64_t l_instHashableArray___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableArray___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instHashableArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instHashableArray(lean_object*, lean_object*);
static const lean_closure_object l_instHashableUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt8_toUInt64___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableUInt8___closed__0 = (const lean_object*)&l_instHashableUInt8___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableUInt8 = (const lean_object*)&l_instHashableUInt8___closed__0_value;
static const lean_closure_object l_instHashableUInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt16_toUInt64___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableUInt16___closed__0 = (const lean_object*)&l_instHashableUInt16___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableUInt16 = (const lean_object*)&l_instHashableUInt16___closed__0_value;
static const lean_closure_object l_instHashableUInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt32_toUInt64___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableUInt32___closed__0 = (const lean_object*)&l_instHashableUInt32___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableUInt32 = (const lean_object*)&l_instHashableUInt32___closed__0_value;
LEAN_EXPORT uint64_t l_instHashableUInt64___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_instHashableUInt64___lam__0___boxed(lean_object*);
static const lean_closure_object l_instHashableUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableUInt64___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableUInt64___closed__0 = (const lean_object*)&l_instHashableUInt64___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableUInt64 = (const lean_object*)&l_instHashableUInt64___closed__0_value;
static const lean_closure_object l_instHashableUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_USize_toUInt64___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableUSize___closed__0 = (const lean_object*)&l_instHashableUSize___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableUSize = (const lean_object*)&l_instHashableUSize___closed__0_value;
LEAN_EXPORT lean_object* l_instHashableFin(lean_object*);
LEAN_EXPORT lean_object* l_instHashableFin___boxed(lean_object*);
LEAN_EXPORT const lean_object* l_instHashableChar = (const lean_object*)&l_instHashableUInt32___closed__0_value;
static lean_once_cell_t l_instHashableInt___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instHashableInt___lam__0___closed__0;
LEAN_EXPORT uint64_t l_instHashableInt___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instHashableInt___lam__0___boxed(lean_object*);
static const lean_closure_object l_instHashableInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableInt___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashableInt___closed__0 = (const lean_object*)&l_instHashableInt___closed__0_value;
LEAN_EXPORT const lean_object* l_instHashableInt = (const lean_object*)&l_instHashableInt___closed__0_value;
LEAN_EXPORT uint64_t l_instHashable___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instHashable___lam__0___boxed(lean_object*);
static const lean_closure_object l_instHashable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashable___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashable___closed__0 = (const lean_object*)&l_instHashable___closed__0_value;
LEAN_EXPORT lean_object* l_instHashable(lean_object*);
LEAN_EXPORT uint64_t l_hash64(uint64_t);
LEAN_EXPORT lean_object* l_hash64___boxed(lean_object*);
LEAN_EXPORT uint64_t l_instHashableProd___redArg___lam__0(lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_x_5_){
_start:
{
lean_object* v_fst_6_; lean_object* v_snd_7_; lean_object* v___x_8_; lean_object* v___x_9_; uint64_t v___x_10_; uint64_t v___x_11_; uint64_t v___x_12_; 
v_fst_6_ = lean_ctor_get(v_x_5_, 0);
lean_inc(v_fst_6_);
v_snd_7_ = lean_ctor_get(v_x_5_, 1);
lean_inc(v_snd_7_);
lean_dec_ref(v_x_5_);
v___x_8_ = lean_apply_1(v_inst_3_, v_fst_6_);
v___x_9_ = lean_apply_1(v_inst_4_, v_snd_7_);
v___x_10_ = lean_unbox_uint64(v___x_8_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_unbox_uint64(v___x_9_);
lean_dec_ref(v___x_9_);
v___x_12_ = lean_uint64_mix_hash(v___x_10_, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object* v_inst_13_, lean_object* v_inst_14_, lean_object* v_x_15_){
_start:
{
uint64_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_instHashableProd___redArg___lam__0(v_inst_13_, v_inst_14_, v_x_15_);
v_r_17_ = lean_box_uint64(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT lean_object* l_instHashableProd___redArg(lean_object* v_inst_18_, lean_object* v_inst_19_){
_start:
{
lean_object* v___f_20_; 
v___f_20_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_20_, 0, v_inst_18_);
lean_closure_set(v___f_20_, 1, v_inst_19_);
return v___f_20_;
}
}
LEAN_EXPORT lean_object* l_instHashableProd(lean_object* v_00_u03b1_21_, lean_object* v_00_u03b2_22_, lean_object* v_inst_23_, lean_object* v_inst_24_){
_start:
{
lean_object* v___f_25_; 
v___f_25_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_25_, 0, v_inst_23_);
lean_closure_set(v___f_25_, 1, v_inst_24_);
return v___f_25_;
}
}
LEAN_EXPORT uint64_t l_instHashableBool___lam__0(uint8_t v_x_26_){
_start:
{
if (v_x_26_ == 0)
{
uint64_t v___x_27_; 
v___x_27_ = 13ULL;
return v___x_27_;
}
else
{
uint64_t v___x_28_; 
v___x_28_ = 11ULL;
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* l_instHashableBool___lam__0___boxed(lean_object* v_x_29_){
_start:
{
uint8_t v_x_32__boxed_30_; uint64_t v_res_31_; lean_object* v_r_32_; 
v_x_32__boxed_30_ = lean_unbox(v_x_29_);
v_res_31_ = l_instHashableBool___lam__0(v_x_32__boxed_30_);
v_r_32_ = lean_box_uint64(v_res_31_);
return v_r_32_;
}
}
LEAN_EXPORT uint64_t l_instHashablePEmpty___lam__0(uint8_t v_x_35_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_instHashablePEmpty___lam__0___boxed(lean_object* v_x_36_){
_start:
{
uint8_t v_x_boxed_37_; uint64_t v_res_38_; lean_object* v_r_39_; 
v_x_boxed_37_ = lean_unbox(v_x_36_);
v_res_38_ = l_instHashablePEmpty___lam__0(v_x_boxed_37_);
v_r_39_ = lean_box_uint64(v_res_38_);
return v_r_39_;
}
}
LEAN_EXPORT uint64_t l_instHashablePUnit___lam__0(lean_object* v_x_42_){
_start:
{
uint64_t v___x_43_; 
v___x_43_ = 11ULL;
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_instHashablePUnit___lam__0___boxed(lean_object* v_x_44_){
_start:
{
uint64_t v_res_45_; lean_object* v_r_46_; 
v_res_45_ = l_instHashablePUnit___lam__0(v_x_44_);
v_r_46_ = lean_box_uint64(v_res_45_);
return v_r_46_;
}
}
LEAN_EXPORT uint64_t l_instHashableOption___redArg___lam__0(lean_object* v_inst_49_, lean_object* v_x_50_){
_start:
{
if (lean_obj_tag(v_x_50_) == 0)
{
uint64_t v___x_51_; 
lean_dec_ref(v_inst_49_);
v___x_51_ = 11ULL;
return v___x_51_;
}
else
{
lean_object* v_val_52_; lean_object* v___x_53_; uint64_t v___x_54_; uint64_t v___x_55_; uint64_t v___x_56_; 
v_val_52_ = lean_ctor_get(v_x_50_, 0);
lean_inc(v_val_52_);
lean_dec_ref(v_x_50_);
v___x_53_ = lean_apply_1(v_inst_49_, v_val_52_);
v___x_54_ = 13ULL;
v___x_55_ = lean_unbox_uint64(v___x_53_);
lean_dec_ref(v___x_53_);
v___x_56_ = lean_uint64_mix_hash(v___x_55_, v___x_54_);
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l_instHashableOption___redArg___lam__0___boxed(lean_object* v_inst_57_, lean_object* v_x_58_){
_start:
{
uint64_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_instHashableOption___redArg___lam__0(v_inst_57_, v_x_58_);
v_r_60_ = lean_box_uint64(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT lean_object* l_instHashableOption___redArg(lean_object* v_inst_61_){
_start:
{
lean_object* v___f_62_; 
v___f_62_ = lean_alloc_closure((void*)(l_instHashableOption___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_62_, 0, v_inst_61_);
return v___f_62_;
}
}
LEAN_EXPORT lean_object* l_instHashableOption(lean_object* v_00_u03b1_63_, lean_object* v_inst_64_){
_start:
{
lean_object* v___f_65_; 
v___f_65_ = lean_alloc_closure((void*)(l_instHashableOption___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_65_, 0, v_inst_64_);
return v___f_65_;
}
}
LEAN_EXPORT uint64_t l_instHashableList___redArg___lam__0(lean_object* v_inst_66_, uint64_t v_r_67_, lean_object* v_a_68_){
_start:
{
lean_object* v___x_69_; uint64_t v___x_70_; uint64_t v___x_71_; 
v___x_69_ = lean_apply_1(v_inst_66_, v_a_68_);
v___x_70_ = lean_unbox_uint64(v___x_69_);
lean_dec_ref(v___x_69_);
v___x_71_ = lean_uint64_mix_hash(v_r_67_, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_instHashableList___redArg___lam__0___boxed(lean_object* v_inst_72_, lean_object* v_r_73_, lean_object* v_a_74_){
_start:
{
uint64_t v_r_boxed_75_; uint64_t v_res_76_; lean_object* v_r_77_; 
v_r_boxed_75_ = lean_unbox_uint64(v_r_73_);
lean_dec_ref(v_r_73_);
v_res_76_ = l_instHashableList___redArg___lam__0(v_inst_72_, v_r_boxed_75_, v_a_74_);
v_r_77_ = lean_box_uint64(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT uint64_t l_instHashableList___redArg___lam__1(lean_object* v___f_80_, lean_object* v_as_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; uint64_t v___x_84_; 
v___x_82_ = ((lean_object*)(l_instHashableList___redArg___lam__1___boxed__const__1));
v___x_83_ = l_List_foldl___redArg(v___f_80_, v___x_82_, v_as_81_);
v___x_84_ = lean_unbox_uint64(v___x_83_);
lean_dec(v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_instHashableList___redArg___lam__1___boxed(lean_object* v___f_85_, lean_object* v_as_86_){
_start:
{
uint64_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_instHashableList___redArg___lam__1(v___f_85_, v_as_86_);
v_r_88_ = lean_box_uint64(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT lean_object* l_instHashableList___redArg(lean_object* v_inst_89_){
_start:
{
lean_object* v___f_90_; lean_object* v___f_91_; 
v___f_90_ = lean_alloc_closure((void*)(l_instHashableList___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_90_, 0, v_inst_89_);
v___f_91_ = lean_alloc_closure((void*)(l_instHashableList___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_91_, 0, v___f_90_);
return v___f_91_;
}
}
LEAN_EXPORT lean_object* l_instHashableList(lean_object* v_00_u03b1_92_, lean_object* v_inst_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_instHashableList___redArg(v_inst_93_);
return v___x_94_;
}
}
LEAN_EXPORT uint64_t l_instHashableArray___redArg___lam__0(lean_object* v_inst_95_, uint64_t v_x1_96_, lean_object* v_x2_97_){
_start:
{
lean_object* v___x_98_; uint64_t v___x_99_; uint64_t v___x_100_; 
v___x_98_ = lean_apply_1(v_inst_95_, v_x2_97_);
v___x_99_ = lean_unbox_uint64(v___x_98_);
lean_dec_ref(v___x_98_);
v___x_100_ = lean_uint64_mix_hash(v_x1_96_, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_instHashableArray___redArg___lam__0___boxed(lean_object* v_inst_101_, lean_object* v_x1_102_, lean_object* v_x2_103_){
_start:
{
uint64_t v_x1_84__boxed_104_; uint64_t v_res_105_; lean_object* v_r_106_; 
v_x1_84__boxed_104_ = lean_unbox_uint64(v_x1_102_);
lean_dec_ref(v_x1_102_);
v_res_105_ = l_instHashableArray___redArg___lam__0(v_inst_101_, v_x1_84__boxed_104_, v_x2_103_);
v_r_106_ = lean_box_uint64(v_res_105_);
return v_r_106_;
}
}
LEAN_EXPORT uint64_t l_instHashableArray___redArg___lam__1(lean_object* v___f_126_, lean_object* v_as_127_){
_start:
{
uint64_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_128_ = 7ULL;
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = lean_array_get_size(v_as_127_);
v___x_131_ = ((lean_object*)(l_instHashableArray___redArg___lam__1___closed__9));
v___x_132_ = lean_nat_dec_lt(v___x_129_, v___x_130_);
if (v___x_132_ == 0)
{
lean_dec_ref(v_as_127_);
lean_dec_ref(v___f_126_);
return v___x_128_;
}
else
{
uint8_t v___x_133_; 
v___x_133_ = lean_nat_dec_le(v___x_130_, v___x_130_);
if (v___x_133_ == 0)
{
if (v___x_132_ == 0)
{
lean_dec_ref(v_as_127_);
lean_dec_ref(v___f_126_);
return v___x_128_;
}
else
{
size_t v___x_134_; size_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; uint64_t v___x_138_; 
v___x_134_ = ((size_t)0ULL);
v___x_135_ = lean_usize_of_nat(v___x_130_);
v___x_136_ = ((lean_object*)(l_instHashableList___redArg___lam__1___boxed__const__1));
v___x_137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_131_, v___f_126_, v_as_127_, v___x_134_, v___x_135_, v___x_136_);
v___x_138_ = lean_unbox_uint64(v___x_137_);
lean_dec(v___x_137_);
return v___x_138_;
}
}
else
{
size_t v___x_139_; size_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; uint64_t v___x_143_; 
v___x_139_ = ((size_t)0ULL);
v___x_140_ = lean_usize_of_nat(v___x_130_);
v___x_141_ = ((lean_object*)(l_instHashableList___redArg___lam__1___boxed__const__1));
v___x_142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_131_, v___f_126_, v_as_127_, v___x_139_, v___x_140_, v___x_141_);
v___x_143_ = lean_unbox_uint64(v___x_142_);
lean_dec(v___x_142_);
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_instHashableArray___redArg___lam__1___boxed(lean_object* v___f_144_, lean_object* v_as_145_){
_start:
{
uint64_t v_res_146_; lean_object* v_r_147_; 
v_res_146_ = l_instHashableArray___redArg___lam__1(v___f_144_, v_as_145_);
v_r_147_ = lean_box_uint64(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT lean_object* l_instHashableArray___redArg(lean_object* v_inst_148_){
_start:
{
lean_object* v___f_149_; lean_object* v___f_150_; 
v___f_149_ = lean_alloc_closure((void*)(l_instHashableArray___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_149_, 0, v_inst_148_);
v___f_150_ = lean_alloc_closure((void*)(l_instHashableArray___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_150_, 0, v___f_149_);
return v___f_150_;
}
}
LEAN_EXPORT lean_object* l_instHashableArray(lean_object* v_00_u03b1_151_, lean_object* v_inst_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_instHashableArray___redArg(v_inst_152_);
return v___x_153_;
}
}
LEAN_EXPORT uint64_t l_instHashableUInt64___lam__0(uint64_t v_n_160_){
_start:
{
return v_n_160_;
}
}
LEAN_EXPORT lean_object* l_instHashableUInt64___lam__0___boxed(lean_object* v_n_161_){
_start:
{
uint64_t v_n_boxed_162_; uint64_t v_res_163_; lean_object* v_r_164_; 
v_n_boxed_162_ = lean_unbox_uint64(v_n_161_);
lean_dec_ref(v_n_161_);
v_res_163_ = l_instHashableUInt64___lam__0(v_n_boxed_162_);
v_r_164_ = lean_box_uint64(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT lean_object* l_instHashableFin(lean_object* v_n_169_){
_start:
{
lean_object* v___f_170_; 
v___f_170_ = ((lean_object*)(l_instHashableNat___closed__0));
return v___f_170_;
}
}
LEAN_EXPORT lean_object* l_instHashableFin___boxed(lean_object* v_n_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_instHashableFin(v_n_171_);
lean_dec(v_n_171_);
return v_res_172_;
}
}
static lean_object* _init_l_instHashableInt___lam__0___closed__0(void){
_start:
{
lean_object* v_natZero_174_; lean_object* v_intZero_175_; 
v_natZero_174_ = lean_unsigned_to_nat(0u);
v_intZero_175_ = lean_nat_to_int(v_natZero_174_);
return v_intZero_175_;
}
}
LEAN_EXPORT uint64_t l_instHashableInt___lam__0(lean_object* v_x_176_){
_start:
{
lean_object* v_intZero_177_; uint8_t v_isNeg_178_; 
v_intZero_177_ = lean_obj_once(&l_instHashableInt___lam__0___closed__0, &l_instHashableInt___lam__0___closed__0_once, _init_l_instHashableInt___lam__0___closed__0);
v_isNeg_178_ = lean_int_dec_lt(v_x_176_, v_intZero_177_);
if (v_isNeg_178_ == 0)
{
lean_object* v_a_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint64_t v___x_182_; 
v_a_179_ = lean_nat_abs(v_x_176_);
v___x_180_ = lean_unsigned_to_nat(2u);
v___x_181_ = lean_nat_mul(v___x_180_, v_a_179_);
lean_dec(v_a_179_);
v___x_182_ = lean_uint64_of_nat(v___x_181_);
lean_dec(v___x_181_);
return v___x_182_;
}
else
{
lean_object* v_abs_183_; lean_object* v_one_184_; lean_object* v_a_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; uint64_t v___x_189_; 
v_abs_183_ = lean_nat_abs(v_x_176_);
v_one_184_ = lean_unsigned_to_nat(1u);
v_a_185_ = lean_nat_sub(v_abs_183_, v_one_184_);
lean_dec(v_abs_183_);
v___x_186_ = lean_unsigned_to_nat(2u);
v___x_187_ = lean_nat_mul(v___x_186_, v_a_185_);
lean_dec(v_a_185_);
v___x_188_ = lean_nat_add(v___x_187_, v_one_184_);
lean_dec(v___x_187_);
v___x_189_ = lean_uint64_of_nat(v___x_188_);
lean_dec(v___x_188_);
return v___x_189_;
}
}
}
LEAN_EXPORT lean_object* l_instHashableInt___lam__0___boxed(lean_object* v_x_190_){
_start:
{
uint64_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_instHashableInt___lam__0(v_x_190_);
lean_dec(v_x_190_);
v_r_192_ = lean_box_uint64(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT uint64_t l_instHashable___lam__0(lean_object* v_x_195_){
_start:
{
uint64_t v___x_196_; 
v___x_196_ = 0ULL;
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_instHashable___lam__0___boxed(lean_object* v_x_197_){
_start:
{
uint64_t v_res_198_; lean_object* v_r_199_; 
v_res_198_ = l_instHashable___lam__0(v_x_197_);
v_r_199_ = lean_box_uint64(v_res_198_);
return v_r_199_;
}
}
LEAN_EXPORT lean_object* l_instHashable(lean_object* v_P_201_){
_start:
{
lean_object* v___f_202_; 
v___f_202_ = ((lean_object*)(l_instHashable___closed__0));
return v___f_202_;
}
}
LEAN_EXPORT uint64_t l_hash64(uint64_t v_u_203_){
_start:
{
uint64_t v___x_204_; uint64_t v___x_205_; 
v___x_204_ = 11ULL;
v___x_205_ = lean_uint64_mix_hash(v_u_203_, v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_hash64___boxed(lean_object* v_u_206_){
_start:
{
uint64_t v_u_boxed_207_; uint64_t v_res_208_; lean_object* v_r_209_; 
v_u_boxed_207_ = lean_unbox_uint64(v_u_206_);
lean_dec_ref(v_u_206_);
v_res_208_ = l_hash64(v_u_boxed_207_);
v_r_209_ = lean_box_uint64(v_res_208_);
return v_r_209_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Hashable(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Hashable(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Hashable(builtin);
}
#ifdef __cplusplus
}
#endif
