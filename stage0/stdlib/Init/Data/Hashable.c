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
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* l_UInt16_toUInt64___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_instHashableList___redArg___lam__1(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_instHashableFin___redArg();
LEAN_EXPORT lean_object* l_instHashableFin___redArg___boxed(lean_object*);
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
LEAN_EXPORT uint64_t l_instHashable___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instHashable___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_instHashable___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashable___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instHashable___redArg___closed__0 = (const lean_object*)&l_instHashable___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_instHashable___redArg();
LEAN_EXPORT lean_object* l_instHashable___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_instHashable(lean_object*);
LEAN_EXPORT uint64_t l_hash64(uint64_t);
LEAN_EXPORT lean_object* l_hash64___boxed(lean_object*);
uint64_t l_instHashableProd___redArg___lam__0(lean_object* v_inst_3_, lean_object* v_inst_4_, lean_object* v_x_5_){
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
LEAN_EXPORT void l_instHashableProd___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_3_ = stack[0].m_obj;
lean_object* v_inst_4_ = stack[1].m_obj;
lean_object* v_x_5_ = stack[2].m_obj;
uint64_t v_res_13_;
v_res_13_ = l_instHashableProd___redArg___lam__0(v_inst_3_, v_inst_4_, v_x_5_);
stack->m_num = v_res_13_;
}
LEAN_EXPORT lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_x_16_){
_start:
{
uint64_t v_res_17_; lean_object* v_r_18_; 
v_res_17_ = l_instHashableProd___redArg___lam__0(v_inst_14_, v_inst_15_, v_x_16_);
v_r_18_ = lean_box_uint64(v_res_17_);
return v_r_18_;
}
}
LEAN_EXPORT lean_object* l_instHashableProd___redArg(lean_object* v_inst_19_, lean_object* v_inst_20_){
_start:
{
lean_object* v___f_21_; 
v___f_21_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_21_, 0, v_inst_19_);
lean_closure_set(v___f_21_, 1, v_inst_20_);
return v___f_21_;
}
}
LEAN_EXPORT lean_object* l_instHashableProd(lean_object* v_00_u03b1_22_, lean_object* v_00_u03b2_23_, lean_object* v_inst_24_, lean_object* v_inst_25_){
_start:
{
lean_object* v___f_26_; 
v___f_26_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_26_, 0, v_inst_24_);
lean_closure_set(v___f_26_, 1, v_inst_25_);
return v___f_26_;
}
}
uint64_t l_instHashableBool___lam__0(uint8_t v_x_27_){
_start:
{
if (v_x_27_ == 0)
{
uint64_t v___x_28_; 
v___x_28_ = 13ULL;
return v___x_28_;
}
else
{
uint64_t v___x_29_; 
v___x_29_ = 11ULL;
return v___x_29_;
}
}
}
LEAN_EXPORT void l_instHashableBool___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_27_ = stack[0].m_num;
uint64_t v_res_30_;
v_res_30_ = l_instHashableBool___lam__0(v_x_27_);
stack->m_num = v_res_30_;
}
LEAN_EXPORT lean_object* l_instHashableBool___lam__0___boxed(lean_object* v_x_31_){
_start:
{
uint8_t v_x_32__boxed_32_; uint64_t v_res_33_; lean_object* v_r_34_; 
v_x_32__boxed_32_ = lean_unbox(v_x_31_);
v_res_33_ = l_instHashableBool___lam__0(v_x_32__boxed_32_);
v_r_34_ = lean_box_uint64(v_res_33_);
return v_r_34_;
}
}
uint64_t l_instHashablePEmpty___lam__0(uint8_t v_x_37_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT void l_instHashablePEmpty___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_37_ = stack[0].m_num;
uint64_t v_res_38_;
v_res_38_ = l_instHashablePEmpty___lam__0(v_x_37_);
stack->m_num = v_res_38_;
}
LEAN_EXPORT lean_object* l_instHashablePEmpty___lam__0___boxed(lean_object* v_x_39_){
_start:
{
uint8_t v_x_boxed_40_; uint64_t v_res_41_; lean_object* v_r_42_; 
v_x_boxed_40_ = lean_unbox(v_x_39_);
v_res_41_ = l_instHashablePEmpty___lam__0(v_x_boxed_40_);
v_r_42_ = lean_box_uint64(v_res_41_);
return v_r_42_;
}
}
uint64_t l_instHashablePUnit___lam__0(lean_object* v_x_45_){
_start:
{
uint64_t v___x_46_; 
v___x_46_ = 11ULL;
return v___x_46_;
}
}
LEAN_EXPORT void l_instHashablePUnit___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_45_ = stack[0].m_obj;
uint64_t v_res_47_;
v_res_47_ = l_instHashablePUnit___lam__0(v_x_45_);
stack->m_num = v_res_47_;
}
LEAN_EXPORT lean_object* l_instHashablePUnit___lam__0___boxed(lean_object* v_x_48_){
_start:
{
uint64_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = l_instHashablePUnit___lam__0(v_x_48_);
v_r_50_ = lean_box_uint64(v_res_49_);
return v_r_50_;
}
}
uint64_t l_instHashableOption___redArg___lam__0(lean_object* v_inst_53_, lean_object* v_x_54_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
uint64_t v___x_55_; 
lean_dec_ref(v_inst_53_);
v___x_55_ = 11ULL;
return v___x_55_;
}
else
{
lean_object* v_val_56_; lean_object* v___x_57_; uint64_t v___x_58_; uint64_t v___x_59_; uint64_t v___x_60_; 
v_val_56_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_val_56_);
lean_dec_ref_known(v_x_54_, 1);
v___x_57_ = lean_apply_1(v_inst_53_, v_val_56_);
v___x_58_ = 13ULL;
v___x_59_ = lean_unbox_uint64(v___x_57_);
lean_dec_ref(v___x_57_);
v___x_60_ = lean_uint64_mix_hash(v___x_59_, v___x_58_);
return v___x_60_;
}
}
}
LEAN_EXPORT void l_instHashableOption___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_53_ = stack[0].m_obj;
lean_object* v_x_54_ = stack[1].m_obj;
uint64_t v_res_61_;
v_res_61_ = l_instHashableOption___redArg___lam__0(v_inst_53_, v_x_54_);
stack->m_num = v_res_61_;
}
LEAN_EXPORT lean_object* l_instHashableOption___redArg___lam__0___boxed(lean_object* v_inst_62_, lean_object* v_x_63_){
_start:
{
uint64_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_instHashableOption___redArg___lam__0(v_inst_62_, v_x_63_);
v_r_65_ = lean_box_uint64(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT lean_object* l_instHashableOption___redArg(lean_object* v_inst_66_){
_start:
{
lean_object* v___f_67_; 
v___f_67_ = lean_alloc_closure((void*)(l_instHashableOption___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_67_, 0, v_inst_66_);
return v___f_67_;
}
}
LEAN_EXPORT lean_object* l_instHashableOption(lean_object* v_00_u03b1_68_, lean_object* v_inst_69_){
_start:
{
lean_object* v___f_70_; 
v___f_70_ = lean_alloc_closure((void*)(l_instHashableOption___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_70_, 0, v_inst_69_);
return v___f_70_;
}
}
uint64_t l_instHashableList___redArg___lam__0(lean_object* v_inst_71_, uint64_t v_r_72_, lean_object* v_a_73_){
_start:
{
lean_object* v___x_74_; uint64_t v___x_75_; uint64_t v___x_76_; 
v___x_74_ = lean_apply_1(v_inst_71_, v_a_73_);
v___x_75_ = lean_unbox_uint64(v___x_74_);
lean_dec_ref(v___x_74_);
v___x_76_ = lean_uint64_mix_hash(v_r_72_, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT void l_instHashableList___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_71_ = stack[0].m_obj;
uint64_t v_r_72_ = stack[1].m_num;
lean_object* v_a_73_ = stack[2].m_obj;
uint64_t v_res_77_;
v_res_77_ = l_instHashableList___redArg___lam__0(v_inst_71_, v_r_72_, v_a_73_);
stack->m_num = v_res_77_;
}
LEAN_EXPORT lean_object* l_instHashableList___redArg___lam__0___boxed(lean_object* v_inst_78_, lean_object* v_r_79_, lean_object* v_a_80_){
_start:
{
uint64_t v_r_boxed_81_; uint64_t v_res_82_; lean_object* v_r_83_; 
v_r_boxed_81_ = lean_unbox_uint64(v_r_79_);
lean_dec_ref(v_r_79_);
v_res_82_ = l_instHashableList___redArg___lam__0(v_inst_78_, v_r_boxed_81_, v_a_80_);
v_r_83_ = lean_box_uint64(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT lean_object* l_instHashableList___redArg___lam__1(lean_object* v___f_86_, lean_object* v_as_87_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = ((lean_object*)(l_instHashableList___redArg___lam__1___boxed__const__1));
v___x_89_ = l_List_foldl___redArg(v___f_86_, v___x_88_, v_as_87_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_instHashableList___redArg(lean_object* v_inst_90_){
_start:
{
lean_object* v___f_91_; lean_object* v___f_92_; 
v___f_91_ = lean_alloc_closure((void*)(l_instHashableList___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_91_, 0, v_inst_90_);
v___f_92_ = lean_alloc_closure((void*)(l_instHashableList___redArg___lam__1), 2, 1);
lean_closure_set(v___f_92_, 0, v___f_91_);
return v___f_92_;
}
}
LEAN_EXPORT lean_object* l_instHashableList(lean_object* v_00_u03b1_93_, lean_object* v_inst_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_instHashableList___redArg(v_inst_94_);
return v___x_95_;
}
}
uint64_t l_instHashableArray___redArg___lam__0(lean_object* v_inst_96_, uint64_t v_x1_97_, lean_object* v_x2_98_){
_start:
{
lean_object* v___x_99_; uint64_t v___x_100_; uint64_t v___x_101_; 
v___x_99_ = lean_apply_1(v_inst_96_, v_x2_98_);
v___x_100_ = lean_unbox_uint64(v___x_99_);
lean_dec_ref(v___x_99_);
v___x_101_ = lean_uint64_mix_hash(v_x1_97_, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT void l_instHashableArray___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_96_ = stack[0].m_obj;
uint64_t v_x1_97_ = stack[1].m_num;
lean_object* v_x2_98_ = stack[2].m_obj;
uint64_t v_res_102_;
v_res_102_ = l_instHashableArray___redArg___lam__0(v_inst_96_, v_x1_97_, v_x2_98_);
stack->m_num = v_res_102_;
}
LEAN_EXPORT lean_object* l_instHashableArray___redArg___lam__0___boxed(lean_object* v_inst_103_, lean_object* v_x1_104_, lean_object* v_x2_105_){
_start:
{
uint64_t v_x1_81__boxed_106_; uint64_t v_res_107_; lean_object* v_r_108_; 
v_x1_81__boxed_106_ = lean_unbox_uint64(v_x1_104_);
lean_dec_ref(v_x1_104_);
v_res_107_ = l_instHashableArray___redArg___lam__0(v_inst_103_, v_x1_81__boxed_106_, v_x2_105_);
v_r_108_ = lean_box_uint64(v_res_107_);
return v_r_108_;
}
}
uint64_t l_instHashableArray___redArg___lam__1(lean_object* v___f_128_, lean_object* v_as_129_){
_start:
{
uint64_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_130_ = 7ULL;
v___x_131_ = lean_unsigned_to_nat(0u);
v___x_132_ = lean_array_get_size(v_as_129_);
v___x_133_ = ((lean_object*)(l_instHashableArray___redArg___lam__1___closed__9));
v___x_134_ = lean_nat_dec_lt(v___x_131_, v___x_132_);
if (v___x_134_ == 0)
{
lean_dec_ref(v_as_129_);
lean_dec_ref(v___f_128_);
return v___x_130_;
}
else
{
uint8_t v___x_135_; 
v___x_135_ = lean_nat_dec_le(v___x_132_, v___x_132_);
if (v___x_135_ == 0)
{
if (v___x_134_ == 0)
{
lean_dec_ref(v_as_129_);
lean_dec_ref(v___f_128_);
return v___x_130_;
}
else
{
size_t v___x_136_; size_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint64_t v___x_140_; 
v___x_136_ = ((size_t)0ULL);
v___x_137_ = lean_usize_of_nat(v___x_132_);
v___x_138_ = ((lean_object*)(l_instHashableList___redArg___lam__1___boxed__const__1));
v___x_139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_133_, v___f_128_, v_as_129_, v___x_136_, v___x_137_, v___x_138_);
v___x_140_ = lean_unbox_uint64(v___x_139_);
lean_dec(v___x_139_);
return v___x_140_;
}
}
else
{
size_t v___x_141_; size_t v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint64_t v___x_145_; 
v___x_141_ = ((size_t)0ULL);
v___x_142_ = lean_usize_of_nat(v___x_132_);
v___x_143_ = ((lean_object*)(l_instHashableList___redArg___lam__1___boxed__const__1));
v___x_144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_133_, v___f_128_, v_as_129_, v___x_141_, v___x_142_, v___x_143_);
v___x_145_ = lean_unbox_uint64(v___x_144_);
lean_dec(v___x_144_);
return v___x_145_;
}
}
}
}
LEAN_EXPORT void l_instHashableArray___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_128_ = stack[0].m_obj;
lean_object* v_as_129_ = stack[1].m_obj;
uint64_t v_res_146_;
v_res_146_ = l_instHashableArray___redArg___lam__1(v___f_128_, v_as_129_);
stack->m_num = v_res_146_;
}
LEAN_EXPORT lean_object* l_instHashableArray___redArg___lam__1___boxed(lean_object* v___f_147_, lean_object* v_as_148_){
_start:
{
uint64_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_instHashableArray___redArg___lam__1(v___f_147_, v_as_148_);
v_r_150_ = lean_box_uint64(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT lean_object* l_instHashableArray___redArg(lean_object* v_inst_151_){
_start:
{
lean_object* v___f_152_; lean_object* v___f_153_; 
v___f_152_ = lean_alloc_closure((void*)(l_instHashableArray___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_152_, 0, v_inst_151_);
v___f_153_ = lean_alloc_closure((void*)(l_instHashableArray___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_153_, 0, v___f_152_);
return v___f_153_;
}
}
LEAN_EXPORT lean_object* l_instHashableArray(lean_object* v_00_u03b1_154_, lean_object* v_inst_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_instHashableArray___redArg(v_inst_155_);
return v___x_156_;
}
}
uint64_t l_instHashableUInt64___lam__0(uint64_t v_n_163_){
_start:
{
return v_n_163_;
}
}
LEAN_EXPORT void l_instHashableUInt64___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_n_163_ = stack[0].m_num;
uint64_t v_res_164_;
v_res_164_ = l_instHashableUInt64___lam__0(v_n_163_);
stack->m_num = v_res_164_;
}
LEAN_EXPORT lean_object* l_instHashableUInt64___lam__0___boxed(lean_object* v_n_165_){
_start:
{
uint64_t v_n_boxed_166_; uint64_t v_res_167_; lean_object* v_r_168_; 
v_n_boxed_166_ = lean_unbox_uint64(v_n_165_);
lean_dec_ref(v_n_165_);
v_res_167_ = l_instHashableUInt64___lam__0(v_n_boxed_166_);
v_r_168_ = lean_box_uint64(v_res_167_);
return v_r_168_;
}
}
lean_object* l_instHashableFin___redArg(){
_start:
{
lean_object* v___f_174_; 
v___f_174_ = ((lean_object*)(l_instHashableNat___closed__0));
return v___f_174_;
}
}
LEAN_EXPORT void l_instHashableFin___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_175_;
v_res_175_ = l_instHashableFin___redArg();
stack->m_obj
 = v_res_175_;
}
LEAN_EXPORT lean_object* l_instHashableFin___redArg___boxed(lean_object* v___dummy_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_instHashableFin___redArg();
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_instHashableFin(lean_object* v_n_178_){
_start:
{
lean_object* v___f_179_; 
v___f_179_ = ((lean_object*)(l_instHashableNat___closed__0));
return v___f_179_;
}
}
LEAN_EXPORT lean_object* l_instHashableFin___boxed(lean_object* v_n_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_instHashableFin(v_n_180_);
lean_dec(v_n_180_);
return v_res_181_;
}
}
static lean_object* _init_l_instHashableInt___lam__0___closed__0(void){
_start:
{
lean_object* v_natZero_183_; lean_object* v_intZero_184_; 
v_natZero_183_ = lean_unsigned_to_nat(0u);
v_intZero_184_ = lean_nat_to_int(v_natZero_183_);
return v_intZero_184_;
}
}
uint64_t l_instHashableInt___lam__0(lean_object* v_x_185_){
_start:
{
lean_object* v_intZero_186_; uint8_t v_isNeg_187_; 
v_intZero_186_ = lean_obj_once(&l_instHashableInt___lam__0___closed__0, &l_instHashableInt___lam__0___closed__0_once, _init_l_instHashableInt___lam__0___closed__0);
v_isNeg_187_ = lean_int_dec_lt(v_x_185_, v_intZero_186_);
if (v_isNeg_187_ == 0)
{
lean_object* v_a_188_; lean_object* v___x_189_; lean_object* v___x_190_; uint64_t v___x_191_; 
v_a_188_ = lean_nat_abs(v_x_185_);
v___x_189_ = lean_unsigned_to_nat(2u);
v___x_190_ = lean_nat_mul(v___x_189_, v_a_188_);
lean_dec(v_a_188_);
v___x_191_ = lean_uint64_of_nat(v___x_190_);
lean_dec(v___x_190_);
return v___x_191_;
}
else
{
lean_object* v_abs_192_; lean_object* v_one_193_; lean_object* v_a_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; uint64_t v___x_198_; 
v_abs_192_ = lean_nat_abs(v_x_185_);
v_one_193_ = lean_unsigned_to_nat(1u);
v_a_194_ = lean_nat_sub(v_abs_192_, v_one_193_);
lean_dec(v_abs_192_);
v___x_195_ = lean_unsigned_to_nat(2u);
v___x_196_ = lean_nat_mul(v___x_195_, v_a_194_);
lean_dec(v_a_194_);
v___x_197_ = lean_nat_add(v___x_196_, v_one_193_);
lean_dec(v___x_196_);
v___x_198_ = lean_uint64_of_nat(v___x_197_);
lean_dec(v___x_197_);
return v___x_198_;
}
}
}
LEAN_EXPORT void l_instHashableInt___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_185_ = stack[0].m_obj;
uint64_t v_res_199_;
v_res_199_ = l_instHashableInt___lam__0(v_x_185_);
stack->m_num = v_res_199_;
}
LEAN_EXPORT lean_object* l_instHashableInt___lam__0___boxed(lean_object* v_x_200_){
_start:
{
uint64_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l_instHashableInt___lam__0(v_x_200_);
lean_dec(v_x_200_);
v_r_202_ = lean_box_uint64(v_res_201_);
return v_r_202_;
}
}
uint64_t l_instHashable___redArg___lam__0(lean_object* v_x_205_){
_start:
{
uint64_t v___x_206_; 
v___x_206_ = 0ULL;
return v___x_206_;
}
}
LEAN_EXPORT void l_instHashable___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_res_207_;
v_res_207_ = l_instHashable___redArg___lam__0(lean_box(0));
stack->m_num = v_res_207_;
}
LEAN_EXPORT lean_object* l_instHashable___redArg___lam__0___boxed(lean_object* v_x_208_){
_start:
{
uint64_t v_res_209_; lean_object* v_r_210_; 
v_res_209_ = l_instHashable___redArg___lam__0(v_x_208_);
v_r_210_ = lean_box_uint64(v_res_209_);
return v_r_210_;
}
}
lean_object* l_instHashable___redArg(){
_start:
{
lean_object* v___f_213_; 
v___f_213_ = ((lean_object*)(l_instHashable___redArg___closed__0));
return v___f_213_;
}
}
LEAN_EXPORT void l_instHashable___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_214_;
v_res_214_ = l_instHashable___redArg();
stack->m_obj
 = v_res_214_;
}
LEAN_EXPORT lean_object* l_instHashable___redArg___boxed(lean_object* v___dummy_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_instHashable___redArg();
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_instHashable(lean_object* v_P_217_){
_start:
{
lean_object* v___f_218_; 
v___f_218_ = ((lean_object*)(l_instHashable___redArg___closed__0));
return v___f_218_;
}
}
uint64_t l_hash64(uint64_t v_u_219_){
_start:
{
uint64_t v___x_220_; uint64_t v___x_221_; 
v___x_220_ = 11ULL;
v___x_221_ = lean_uint64_mix_hash(v_u_219_, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT void l_hash64_0interp(lean_interpreter_value* stack)
{
uint64_t v_u_219_ = stack[0].m_num;
uint64_t v_res_222_;
v_res_222_ = l_hash64(v_u_219_);
stack->m_num = v_res_222_;
}
LEAN_EXPORT lean_object* l_hash64___boxed(lean_object* v_u_223_){
_start:
{
uint64_t v_u_boxed_224_; uint64_t v_res_225_; lean_object* v_r_226_; 
v_u_boxed_224_ = lean_unbox_uint64(v_u_223_);
lean_dec_ref(v_u_223_);
v_res_225_ = l_hash64(v_u_boxed_224_);
v_r_226_ = lean_box_uint64(v_res_225_);
return v_r_226_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
