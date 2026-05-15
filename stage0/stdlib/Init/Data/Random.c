// Lean compiler output
// Module: Init.Data.Random
// Imports: public import Init.System.IO import Init.Data.ByteArray.Extra
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_io_get_random_bytes(size_t);
uint64_t l_ByteArray_toUInt64LE_x21(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkStdGen(lean_object*);
LEAN_EXPORT lean_object* l_mkStdGen___boxed(lean_object*);
static lean_once_cell_t l_instInhabitedStdGen___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instInhabitedStdGen___closed__0;
LEAN_EXPORT lean_object* l_instInhabitedStdGen;
static const lean_ctor_object l_stdRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(2147483562) << 1) | 1))}};
static const lean_object* l_stdRange___closed__0 = (const lean_object*)&l_stdRange___closed__0_value;
LEAN_EXPORT const lean_object* l_stdRange = (const lean_object*)&l_stdRange___closed__0_value;
static const lean_string_object l_instReprStdGen___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l_instReprStdGen___lam__0___closed__0 = (const lean_object*)&l_instReprStdGen___lam__0___closed__0_value;
static const lean_string_object l_instReprStdGen___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_instReprStdGen___lam__0___closed__1 = (const lean_object*)&l_instReprStdGen___lam__0___closed__1_value;
static const lean_ctor_object l_instReprStdGen___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprStdGen___lam__0___closed__1_value)}};
static const lean_object* l_instReprStdGen___lam__0___closed__2 = (const lean_object*)&l_instReprStdGen___lam__0___closed__2_value;
static const lean_string_object l_instReprStdGen___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l_instReprStdGen___lam__0___closed__3 = (const lean_object*)&l_instReprStdGen___lam__0___closed__3_value;
static lean_once_cell_t l_instReprStdGen___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instReprStdGen___lam__0___closed__4;
static lean_once_cell_t l_instReprStdGen___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instReprStdGen___lam__0___closed__5;
static const lean_ctor_object l_instReprStdGen___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprStdGen___lam__0___closed__0_value)}};
static const lean_object* l_instReprStdGen___lam__0___closed__6 = (const lean_object*)&l_instReprStdGen___lam__0___closed__6_value;
static const lean_ctor_object l_instReprStdGen___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprStdGen___lam__0___closed__3_value)}};
static const lean_object* l_instReprStdGen___lam__0___closed__7 = (const lean_object*)&l_instReprStdGen___lam__0___closed__7_value;
LEAN_EXPORT lean_object* l_instReprStdGen___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprStdGen___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_instReprStdGen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprStdGen___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instReprStdGen___closed__0 = (const lean_object*)&l_instReprStdGen___closed__0_value;
LEAN_EXPORT const lean_object* l_instReprStdGen = (const lean_object*)&l_instReprStdGen___closed__0_value;
static lean_once_cell_t l_stdNext___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__0;
static lean_once_cell_t l_stdNext___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__1;
static lean_once_cell_t l_stdNext___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__2;
static lean_once_cell_t l_stdNext___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__3;
static lean_once_cell_t l_stdNext___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__4;
static lean_once_cell_t l_stdNext___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__5;
static lean_once_cell_t l_stdNext___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__6;
static lean_once_cell_t l_stdNext___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__7;
static lean_once_cell_t l_stdNext___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__8;
static lean_once_cell_t l_stdNext___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__9;
static lean_once_cell_t l_stdNext___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_stdNext___closed__10;
LEAN_EXPORT lean_object* l_stdNext(lean_object*);
LEAN_EXPORT lean_object* l_stdSplit(lean_object*);
LEAN_EXPORT lean_object* l_instRandomGenStdGen___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_instRandomGenStdGen___lam__0___boxed(lean_object*);
static const lean_closure_object l_instRandomGenStdGen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instRandomGenStdGen___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instRandomGenStdGen___closed__0 = (const lean_object*)&l_instRandomGenStdGen___closed__0_value;
static const lean_closure_object l_instRandomGenStdGen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_stdNext, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instRandomGenStdGen___closed__1 = (const lean_object*)&l_instRandomGenStdGen___closed__1_value;
static const lean_closure_object l_instRandomGenStdGen___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_stdSplit, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instRandomGenStdGen___closed__2 = (const lean_object*)&l_instRandomGenStdGen___closed__2_value;
static const lean_ctor_object l_instRandomGenStdGen___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_instRandomGenStdGen___closed__0_value),((lean_object*)&l_instRandomGenStdGen___closed__1_value),((lean_object*)&l_instRandomGenStdGen___closed__2_value)}};
static const lean_object* l_instRandomGenStdGen___closed__3 = (const lean_object*)&l_instRandomGenStdGen___closed__3_value;
LEAN_EXPORT const lean_object* l_instRandomGenStdGen = (const lean_object*)&l_instRandomGenStdGen___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randBool___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randBool(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__initFn_00___x40_Init_Data_Random_2456098205____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__initFn_00___x40_Init_Data_Random_2456098205____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_stdGenRef;
LEAN_EXPORT lean_object* l_IO_setRandSeed(lean_object*);
LEAN_EXPORT lean_object* l_IO_setRandSeed___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00IO_rand_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00IO_rand_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___at___00IO_rand_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_randNat___at___00IO_rand_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_rand(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_rand___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkStdGen(lean_object* v_s_1_){
_start:
{
lean_object* v___x_2_; lean_object* v_q_3_; lean_object* v_s1_4_; lean_object* v___x_5_; lean_object* v_s2_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_2_ = lean_unsigned_to_nat(2147483562u);
v_q_3_ = lean_nat_div(v_s_1_, v___x_2_);
v_s1_4_ = lean_nat_mod(v_s_1_, v___x_2_);
v___x_5_ = lean_unsigned_to_nat(2147483398u);
v_s2_6_ = lean_nat_mod(v_q_3_, v___x_5_);
lean_dec(v_q_3_);
v___x_7_ = lean_unsigned_to_nat(1u);
v___x_8_ = lean_nat_add(v_s1_4_, v___x_7_);
lean_dec(v_s1_4_);
v___x_9_ = lean_nat_add(v_s2_6_, v___x_7_);
lean_dec(v_s2_6_);
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_8_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_mkStdGen___boxed(lean_object* v_s_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_mkStdGen(v_s_11_);
lean_dec(v_s_11_);
return v_res_12_;
}
}
static lean_object* _init_l_instInhabitedStdGen___closed__0(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = l_mkStdGen(v___x_13_);
return v___x_14_;
}
}
static lean_object* _init_l_instInhabitedStdGen(void){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_obj_once(&l_instInhabitedStdGen___closed__0, &l_instInhabitedStdGen___closed__0_once, _init_l_instInhabitedStdGen___closed__0);
return v___x_15_;
}
}
static lean_object* _init_l_instReprStdGen___lam__0___closed__4(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = ((lean_object*)(l_instReprStdGen___lam__0___closed__0));
v___x_26_ = lean_string_length(v___x_25_);
return v___x_26_;
}
}
static lean_object* _init_l_instReprStdGen___lam__0___closed__5(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_obj_once(&l_instReprStdGen___lam__0___closed__4, &l_instReprStdGen___lam__0___closed__4_once, _init_l_instReprStdGen___lam__0___closed__4);
v___x_28_ = lean_nat_to_int(v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_instReprStdGen___lam__0(lean_object* v_x_33_, lean_object* v_x_34_){
_start:
{
lean_object* v_s1_35_; lean_object* v_s2_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_57_; 
v_s1_35_ = lean_ctor_get(v_x_33_, 0);
v_s2_36_ = lean_ctor_get(v_x_33_, 1);
v_isSharedCheck_57_ = !lean_is_exclusive(v_x_33_);
if (v_isSharedCheck_57_ == 0)
{
v___x_38_ = v_x_33_;
v_isShared_39_ = v_isSharedCheck_57_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_s2_36_);
lean_inc(v_s1_35_);
lean_dec(v_x_33_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_57_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_44_; 
v___x_40_ = l_Nat_reprFast(v_s1_35_);
v___x_41_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
v___x_42_ = ((lean_object*)(l_instReprStdGen___lam__0___closed__2));
if (v_isShared_39_ == 0)
{
lean_ctor_set_tag(v___x_38_, 5);
lean_ctor_set(v___x_38_, 1, v___x_42_);
lean_ctor_set(v___x_38_, 0, v___x_41_);
v___x_44_ = v___x_38_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_41_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v___x_42_);
v___x_44_ = v_reuseFailAlloc_56_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; lean_object* v___x_55_; 
v___x_45_ = l_Nat_reprFast(v_s2_36_);
v___x_46_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
v___x_47_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_44_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
v___x_48_ = lean_obj_once(&l_instReprStdGen___lam__0___closed__5, &l_instReprStdGen___lam__0___closed__5_once, _init_l_instReprStdGen___lam__0___closed__5);
v___x_49_ = ((lean_object*)(l_instReprStdGen___lam__0___closed__6));
v___x_50_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_47_);
v___x_51_ = ((lean_object*)(l_instReprStdGen___lam__0___closed__7));
v___x_52_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_52_, 0, v___x_50_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
v___x_53_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_48_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
v___x_54_ = 0;
v___x_55_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_55_, 0, v___x_53_);
lean_ctor_set_uint8(v___x_55_, sizeof(void*)*1, v___x_54_);
return v___x_55_;
}
}
}
}
LEAN_EXPORT lean_object* l_instReprStdGen___lam__0___boxed(lean_object* v_x_58_, lean_object* v_x_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_instReprStdGen___lam__0(v_x_58_, v_x_59_);
lean_dec(v_x_59_);
return v_res_60_;
}
}
static lean_object* _init_l_stdNext___closed__0(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_unsigned_to_nat(1u);
v___x_64_ = lean_nat_to_int(v___x_63_);
return v___x_64_;
}
}
static lean_object* _init_l_stdNext___closed__1(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_unsigned_to_nat(2147483562u);
v___x_66_ = lean_nat_to_int(v___x_65_);
return v___x_66_;
}
}
static lean_object* _init_l_stdNext___closed__2(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_unsigned_to_nat(40014u);
v___x_68_ = lean_nat_to_int(v___x_67_);
return v___x_68_;
}
}
static lean_object* _init_l_stdNext___closed__3(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(53668u);
v___x_70_ = lean_nat_to_int(v___x_69_);
return v___x_70_;
}
}
static lean_object* _init_l_stdNext___closed__4(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(12211u);
v___x_72_ = lean_nat_to_int(v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l_stdNext___closed__5(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = lean_nat_to_int(v___x_73_);
return v___x_74_;
}
}
static lean_object* _init_l_stdNext___closed__6(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(40692u);
v___x_76_ = lean_nat_to_int(v___x_75_);
return v___x_76_;
}
}
static lean_object* _init_l_stdNext___closed__7(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(52774u);
v___x_78_ = lean_nat_to_int(v___x_77_);
return v___x_78_;
}
}
static lean_object* _init_l_stdNext___closed__8(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = lean_unsigned_to_nat(3791u);
v___x_80_ = lean_nat_to_int(v___x_79_);
return v___x_80_;
}
}
static lean_object* _init_l_stdNext___closed__9(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_unsigned_to_nat(2147483399u);
v___x_82_ = lean_nat_to_int(v___x_81_);
return v___x_82_;
}
}
static lean_object* _init_l_stdNext___closed__10(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(2147483563u);
v___x_84_ = lean_nat_to_int(v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_stdNext(lean_object* v_x_85_){
_start:
{
lean_object* v___y_87_; lean_object* v___y_88_; lean_object* v___y_89_; lean_object* v___y_93_; lean_object* v___y_94_; lean_object* v_s1_106_; lean_object* v_s2_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v_k_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v_s1_x27_119_; lean_object* v___x_120_; lean_object* v___y_122_; uint8_t v___x_140_; 
v_s1_106_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_s1_106_);
v_s2_107_ = lean_ctor_get(v_x_85_, 1);
lean_inc(v_s2_107_);
lean_dec_ref(v_x_85_);
v___x_108_ = lean_unsigned_to_nat(53668u);
v___x_109_ = lean_nat_div(v_s1_106_, v___x_108_);
v_k_110_ = lean_nat_to_int(v___x_109_);
v___x_111_ = lean_obj_once(&l_stdNext___closed__2, &l_stdNext___closed__2_once, _init_l_stdNext___closed__2);
v___x_112_ = lean_nat_to_int(v_s1_106_);
v___x_113_ = lean_obj_once(&l_stdNext___closed__3, &l_stdNext___closed__3_once, _init_l_stdNext___closed__3);
v___x_114_ = lean_int_mul(v_k_110_, v___x_113_);
v___x_115_ = lean_int_sub(v___x_112_, v___x_114_);
lean_dec(v___x_114_);
lean_dec(v___x_112_);
v___x_116_ = lean_int_mul(v___x_111_, v___x_115_);
lean_dec(v___x_115_);
v___x_117_ = lean_obj_once(&l_stdNext___closed__4, &l_stdNext___closed__4_once, _init_l_stdNext___closed__4);
v___x_118_ = lean_int_mul(v_k_110_, v___x_117_);
lean_dec(v_k_110_);
v_s1_x27_119_ = lean_int_sub(v___x_116_, v___x_118_);
lean_dec(v___x_118_);
lean_dec(v___x_116_);
v___x_120_ = lean_obj_once(&l_stdNext___closed__5, &l_stdNext___closed__5_once, _init_l_stdNext___closed__5);
v___x_140_ = lean_int_dec_lt(v_s1_x27_119_, v___x_120_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; 
v___x_141_ = l_Int_toNat(v_s1_x27_119_);
lean_dec(v_s1_x27_119_);
v___y_122_ = v___x_141_;
goto v___jp_121_;
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_142_ = lean_obj_once(&l_stdNext___closed__10, &l_stdNext___closed__10_once, _init_l_stdNext___closed__10);
v___x_143_ = lean_int_add(v_s1_x27_119_, v___x_142_);
lean_dec(v_s1_x27_119_);
v___x_144_ = l_Int_toNat(v___x_143_);
lean_dec(v___x_143_);
v___y_122_ = v___x_144_;
goto v___jp_121_;
}
v___jp_86_:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_90_, 0, v___y_87_);
lean_ctor_set(v___x_90_, 1, v___y_88_);
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v___y_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
return v___x_91_;
}
v___jp_92_:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v_z_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
lean_inc(v___y_93_);
v___x_95_ = lean_nat_to_int(v___y_93_);
lean_inc(v___y_94_);
v___x_96_ = lean_nat_to_int(v___y_94_);
v_z_97_ = lean_int_sub(v___x_95_, v___x_96_);
lean_dec(v___x_96_);
lean_dec(v___x_95_);
v___x_98_ = lean_obj_once(&l_stdNext___closed__0, &l_stdNext___closed__0_once, _init_l_stdNext___closed__0);
v___x_99_ = lean_int_dec_lt(v_z_97_, v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = l_Int_toNat(v_z_97_);
lean_dec(v_z_97_);
v___x_101_ = lean_unsigned_to_nat(2147483562u);
v___x_102_ = lean_nat_mod(v___x_100_, v___x_101_);
lean_dec(v___x_100_);
v___y_87_ = v___y_93_;
v___y_88_ = v___y_94_;
v___y_89_ = v___x_102_;
goto v___jp_86_;
}
else
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_obj_once(&l_stdNext___closed__1, &l_stdNext___closed__1_once, _init_l_stdNext___closed__1);
v___x_104_ = lean_int_add(v_z_97_, v___x_103_);
lean_dec(v_z_97_);
v___x_105_ = l_Int_toNat(v___x_104_);
lean_dec(v___x_104_);
v___y_87_ = v___y_93_;
v___y_88_ = v___y_94_;
v___y_89_ = v___x_105_;
goto v___jp_86_;
}
}
v___jp_121_:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_k_x27_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v_s2_x27_134_; uint8_t v___x_135_; 
v___x_123_ = lean_unsigned_to_nat(52774u);
v___x_124_ = lean_nat_div(v_s2_107_, v___x_123_);
v_k_x27_125_ = lean_nat_to_int(v___x_124_);
v___x_126_ = lean_obj_once(&l_stdNext___closed__6, &l_stdNext___closed__6_once, _init_l_stdNext___closed__6);
v___x_127_ = lean_nat_to_int(v_s2_107_);
v___x_128_ = lean_obj_once(&l_stdNext___closed__7, &l_stdNext___closed__7_once, _init_l_stdNext___closed__7);
v___x_129_ = lean_int_mul(v_k_x27_125_, v___x_128_);
v___x_130_ = lean_int_sub(v___x_127_, v___x_129_);
lean_dec(v___x_129_);
lean_dec(v___x_127_);
v___x_131_ = lean_int_mul(v___x_126_, v___x_130_);
lean_dec(v___x_130_);
v___x_132_ = lean_obj_once(&l_stdNext___closed__8, &l_stdNext___closed__8_once, _init_l_stdNext___closed__8);
v___x_133_ = lean_int_mul(v_k_x27_125_, v___x_132_);
lean_dec(v_k_x27_125_);
v_s2_x27_134_ = lean_int_sub(v___x_131_, v___x_133_);
lean_dec(v___x_133_);
lean_dec(v___x_131_);
v___x_135_ = lean_int_dec_lt(v_s2_x27_134_, v___x_120_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; 
v___x_136_ = l_Int_toNat(v_s2_x27_134_);
lean_dec(v_s2_x27_134_);
v___y_93_ = v___y_122_;
v___y_94_ = v___x_136_;
goto v___jp_92_;
}
else
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = lean_obj_once(&l_stdNext___closed__9, &l_stdNext___closed__9_once, _init_l_stdNext___closed__9);
v___x_138_ = lean_int_add(v_s2_x27_134_, v___x_137_);
lean_dec(v_s2_x27_134_);
v___x_139_ = l_Int_toNat(v___x_138_);
lean_dec(v___x_138_);
v___y_93_ = v___y_122_;
v___y_94_ = v___x_139_;
goto v___jp_92_;
}
}
}
}
LEAN_EXPORT lean_object* l_stdSplit(lean_object* v_x_145_){
_start:
{
lean_object* v___y_147_; lean_object* v___y_148_; lean_object* v_s1_169_; lean_object* v_s2_170_; lean_object* v___y_172_; lean_object* v___x_177_; uint8_t v___x_178_; 
v_s1_169_ = lean_ctor_get(v_x_145_, 0);
v_s2_170_ = lean_ctor_get(v_x_145_, 1);
v___x_177_ = lean_unsigned_to_nat(2147483562u);
v___x_178_ = lean_nat_dec_eq(v_s1_169_, v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_180_ = lean_nat_add(v_s1_169_, v___x_179_);
v___y_172_ = v___x_180_;
goto v___jp_171_;
}
else
{
lean_object* v___x_181_; 
v___x_181_ = lean_unsigned_to_nat(1u);
v___y_172_ = v___x_181_;
goto v___jp_171_;
}
v___jp_146_:
{
lean_object* v___x_149_; lean_object* v_snd_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_167_; 
v___x_149_ = l_stdNext(v_x_145_);
v_snd_150_ = lean_ctor_get(v___x_149_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_167_ == 0)
{
lean_object* v_unused_168_; 
v_unused_168_ = lean_ctor_get(v___x_149_, 0);
lean_dec(v_unused_168_);
v___x_152_ = v___x_149_;
v_isShared_153_ = v_isSharedCheck_167_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_snd_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_167_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v_s1_154_; lean_object* v_s2_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_166_; 
v_s1_154_ = lean_ctor_get(v_snd_150_, 0);
v_s2_155_ = lean_ctor_get(v_snd_150_, 1);
v_isSharedCheck_166_ = !lean_is_exclusive(v_snd_150_);
if (v_isSharedCheck_166_ == 0)
{
v___x_157_ = v_snd_150_;
v_isShared_158_ = v_isSharedCheck_166_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_s2_155_);
lean_inc(v_s1_154_);
lean_dec(v_snd_150_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_166_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v_leftG_160_; 
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___y_147_);
v_leftG_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___y_147_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_s2_155_);
v_leftG_160_ = v_reuseFailAlloc_165_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v_rightG_161_; lean_object* v___x_163_; 
v_rightG_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_rightG_161_, 0, v_s1_154_);
lean_ctor_set(v_rightG_161_, 1, v___y_148_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 1, v_rightG_161_);
lean_ctor_set(v___x_152_, 0, v_leftG_160_);
v___x_163_ = v___x_152_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_leftG_160_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_rightG_161_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
}
v___jp_171_:
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = lean_nat_dec_eq(v_s2_170_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
v___x_175_ = lean_nat_sub(v_s2_170_, v___x_173_);
v___y_147_ = v___y_172_;
v___y_148_ = v___x_175_;
goto v___jp_146_;
}
else
{
lean_object* v___x_176_; 
v___x_176_ = lean_unsigned_to_nat(2147483398u);
v___y_147_ = v___y_172_;
v___y_148_ = v___x_176_;
goto v___jp_146_;
}
}
}
}
LEAN_EXPORT lean_object* l_instRandomGenStdGen___lam__0(lean_object* v_x_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = ((lean_object*)(l_stdRange));
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_instRandomGenStdGen___lam__0___boxed(lean_object* v_x_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_instRandomGenStdGen___lam__0(v_x_184_);
lean_dec_ref(v_x_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___redArg(lean_object* v_inst_194_, lean_object* v_genLo_195_, lean_object* v_genMag_196_, lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
lean_object* v_zero_199_; uint8_t v_isZero_200_; 
v_zero_199_ = lean_unsigned_to_nat(0u);
v_isZero_200_ = lean_nat_dec_eq(v_x_197_, v_zero_199_);
if (v_isZero_200_ == 1)
{
lean_dec(v_x_197_);
lean_dec_ref(v_inst_194_);
return v_x_198_;
}
else
{
lean_object* v_fst_201_; lean_object* v_snd_202_; lean_object* v_next_203_; lean_object* v___x_204_; lean_object* v_fst_205_; lean_object* v_snd_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_220_; 
v_fst_201_ = lean_ctor_get(v_x_198_, 0);
lean_inc(v_fst_201_);
v_snd_202_ = lean_ctor_get(v_x_198_, 1);
lean_inc(v_snd_202_);
lean_dec_ref(v_x_198_);
v_next_203_ = lean_ctor_get(v_inst_194_, 1);
lean_inc_ref(v_next_203_);
v___x_204_ = lean_apply_1(v_next_203_, v_snd_202_);
v_fst_205_ = lean_ctor_get(v___x_204_, 0);
v_snd_206_ = lean_ctor_get(v___x_204_, 1);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_220_ == 0)
{
v___x_208_ = v___x_204_;
v_isShared_209_ = v_isSharedCheck_220_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_snd_206_);
lean_inc(v_fst_205_);
lean_dec(v___x_204_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_220_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v_v_x27_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_217_; 
v___x_210_ = lean_nat_mul(v_fst_201_, v_genMag_196_);
lean_dec(v_fst_201_);
v___x_211_ = lean_nat_sub(v_fst_205_, v_genLo_195_);
lean_dec(v_fst_205_);
v_v_x27_212_ = lean_nat_add(v___x_210_, v___x_211_);
lean_dec(v___x_211_);
lean_dec(v___x_210_);
v___x_213_ = lean_nat_div(v_x_197_, v_genMag_196_);
lean_dec(v_x_197_);
v___x_214_ = lean_unsigned_to_nat(1u);
v___x_215_ = lean_nat_sub(v___x_213_, v___x_214_);
lean_dec(v___x_213_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v_v_x27_212_);
v___x_217_ = v___x_208_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_v_x27_212_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_snd_206_);
v___x_217_ = v_reuseFailAlloc_219_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
v_x_197_ = v___x_215_;
v_x_198_ = v___x_217_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___redArg___boxed(lean_object* v_inst_221_, lean_object* v_genLo_222_, lean_object* v_genMag_223_, lean_object* v_x_224_, lean_object* v_x_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Init_Data_Random_0__randNatAux___redArg(v_inst_221_, v_genLo_222_, v_genMag_223_, v_x_224_, v_x_225_);
lean_dec(v_genMag_223_);
lean_dec(v_genLo_222_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux(lean_object* v_gen_227_, lean_object* v_inst_228_, lean_object* v_genLo_229_, lean_object* v_genMag_230_, lean_object* v_x_231_, lean_object* v_x_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l___private_Init_Data_Random_0__randNatAux___redArg(v_inst_228_, v_genLo_229_, v_genMag_230_, v_x_231_, v_x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___boxed(lean_object* v_gen_234_, lean_object* v_inst_235_, lean_object* v_genLo_236_, lean_object* v_genMag_237_, lean_object* v_x_238_, lean_object* v_x_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l___private_Init_Data_Random_0__randNatAux(v_gen_234_, v_inst_235_, v_genLo_236_, v_genMag_237_, v_x_238_, v_x_239_);
lean_dec(v_genMag_237_);
lean_dec(v_genLo_236_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_randNat___redArg(lean_object* v_inst_241_, lean_object* v_g_242_, lean_object* v_lo_243_, lean_object* v_hi_244_){
_start:
{
lean_object* v___y_246_; lean_object* v___y_247_; uint8_t v___x_279_; lean_object* v___y_281_; 
v___x_279_ = lean_nat_dec_lt(v_hi_244_, v_lo_243_);
if (v___x_279_ == 0)
{
v___y_281_ = v_lo_243_;
goto v___jp_280_;
}
else
{
v___y_281_ = v_hi_244_;
goto v___jp_280_;
}
v___jp_245_:
{
lean_object* v_range_248_; lean_object* v___x_249_; lean_object* v_fst_250_; lean_object* v_snd_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_278_; 
v_range_248_ = lean_ctor_get(v_inst_241_, 0);
lean_inc_ref(v_range_248_);
lean_inc(v_g_242_);
v___x_249_ = lean_apply_1(v_range_248_, v_g_242_);
v_fst_250_ = lean_ctor_get(v___x_249_, 0);
v_snd_251_ = lean_ctor_get(v___x_249_, 1);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_278_ == 0)
{
v___x_253_ = v___x_249_;
v_isShared_254_ = v_isSharedCheck_278_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_snd_251_);
lean_inc(v_fst_250_);
lean_dec(v___x_249_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_278_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v_genMag_257_; lean_object* v_q_258_; lean_object* v___x_259_; lean_object* v_k_260_; lean_object* v_tgtMag_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_255_ = lean_nat_sub(v_snd_251_, v_fst_250_);
lean_dec(v_snd_251_);
v___x_256_ = lean_unsigned_to_nat(1u);
v_genMag_257_ = lean_nat_add(v___x_255_, v___x_256_);
lean_dec(v___x_255_);
v_q_258_ = lean_unsigned_to_nat(1000u);
v___x_259_ = lean_nat_sub(v___y_247_, v___y_246_);
v_k_260_ = lean_nat_add(v___x_259_, v___x_256_);
lean_dec(v___x_259_);
v_tgtMag_261_ = lean_nat_mul(v_k_260_, v_q_258_);
v___x_262_ = lean_unsigned_to_nat(0u);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 1, v_g_242_);
lean_ctor_set(v___x_253_, 0, v___x_262_);
v___x_264_ = v___x_253_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_g_242_);
v___x_264_ = v_reuseFailAlloc_277_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_265_; lean_object* v_fst_266_; lean_object* v_snd_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_276_; 
v___x_265_ = l___private_Init_Data_Random_0__randNatAux___redArg(v_inst_241_, v_fst_250_, v_genMag_257_, v_tgtMag_261_, v___x_264_);
lean_dec(v_genMag_257_);
lean_dec(v_fst_250_);
v_fst_266_ = lean_ctor_get(v___x_265_, 0);
v_snd_267_ = lean_ctor_get(v___x_265_, 1);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_276_ == 0)
{
v___x_269_ = v___x_265_;
v_isShared_270_ = v_isSharedCheck_276_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_snd_267_);
lean_inc(v_fst_266_);
lean_dec(v___x_265_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_276_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v_v_x27_272_; lean_object* v___x_274_; 
v___x_271_ = lean_nat_mod(v_fst_266_, v_k_260_);
lean_dec(v_k_260_);
lean_dec(v_fst_266_);
v_v_x27_272_ = lean_nat_add(v___y_246_, v___x_271_);
lean_dec(v___x_271_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v_v_x27_272_);
v___x_274_ = v___x_269_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_v_x27_272_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_snd_267_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
v___jp_280_:
{
if (v___x_279_ == 0)
{
v___y_246_ = v___y_281_;
v___y_247_ = v_hi_244_;
goto v___jp_245_;
}
else
{
v___y_246_ = v___y_281_;
v___y_247_ = v_lo_243_;
goto v___jp_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_randNat___redArg___boxed(lean_object* v_inst_282_, lean_object* v_g_283_, lean_object* v_lo_284_, lean_object* v_hi_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_randNat___redArg(v_inst_282_, v_g_283_, v_lo_284_, v_hi_285_);
lean_dec(v_hi_285_);
lean_dec(v_lo_284_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_randNat(lean_object* v_gen_287_, lean_object* v_inst_288_, lean_object* v_g_289_, lean_object* v_lo_290_, lean_object* v_hi_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_randNat___redArg(v_inst_288_, v_g_289_, v_lo_290_, v_hi_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_randNat___boxed(lean_object* v_gen_293_, lean_object* v_inst_294_, lean_object* v_g_295_, lean_object* v_lo_296_, lean_object* v_hi_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_randNat(v_gen_293_, v_inst_294_, v_g_295_, v_lo_296_, v_hi_297_);
lean_dec(v_hi_297_);
lean_dec(v_lo_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_randBool___redArg(lean_object* v_inst_299_, lean_object* v_g_300_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v_fst_304_; lean_object* v_snd_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_314_; 
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = l_randNat___redArg(v_inst_299_, v_g_300_, v___x_301_, v___x_302_);
v_fst_304_ = lean_ctor_get(v___x_303_, 0);
v_snd_305_ = lean_ctor_get(v___x_303_, 1);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_314_ == 0)
{
v___x_307_ = v___x_303_;
v_isShared_308_ = v_isSharedCheck_314_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_snd_305_);
lean_inc(v_fst_304_);
lean_dec(v___x_303_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_314_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
uint8_t v___x_309_; lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_309_ = lean_nat_dec_eq(v_fst_304_, v___x_302_);
lean_dec(v_fst_304_);
v___x_310_ = lean_box(v___x_309_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_310_);
v___x_312_ = v___x_307_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_snd_305_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* l_randBool(lean_object* v_gen_315_, lean_object* v_inst_316_, lean_object* v_g_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_randBool___redArg(v_inst_316_, v_g_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__initFn_00___x40_Init_Data_Random_2456098205____hygCtx___hyg_2_(){
_start:
{
size_t v___x_320_; lean_object* v___x_321_; 
v___x_320_ = ((size_t)8ULL);
v___x_321_ = lean_io_get_random_bytes(v___x_320_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_333_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_333_ == 0)
{
v___x_324_ = v___x_321_;
v_isShared_325_ = v_isSharedCheck_333_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_321_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_333_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
uint64_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_326_ = l_ByteArray_toUInt64LE_x21(v_a_322_);
lean_dec(v_a_322_);
v___x_327_ = lean_uint64_to_nat(v___x_326_);
v___x_328_ = l_mkStdGen(v___x_327_);
lean_dec(v___x_327_);
v___x_329_ = lean_st_mk_ref(v___x_328_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v___x_329_);
v___x_331_ = v___x_324_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
v_a_334_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___x_321_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_321_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__initFn_00___x40_Init_Data_Random_2456098205____hygCtx___hyg_2____boxed(lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l___private_Init_Data_Random_0__initFn_00___x40_Init_Data_Random_2456098205____hygCtx___hyg_2_();
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_IO_setRandSeed(lean_object* v_n_344_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = l_IO_stdGenRef;
v___x_347_ = l_mkStdGen(v_n_344_);
v___x_348_ = lean_st_ref_set(v___x_346_, v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_IO_setRandSeed___boxed(lean_object* v_n_349_, lean_object* v_a_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_IO_setRandSeed(v_n_349_);
lean_dec(v_n_349_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00IO_rand_spec__0_spec__0(lean_object* v_genLo_352_, lean_object* v_genMag_353_, lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
lean_object* v_zero_356_; uint8_t v_isZero_357_; 
v_zero_356_ = lean_unsigned_to_nat(0u);
v_isZero_357_ = lean_nat_dec_eq(v_x_354_, v_zero_356_);
if (v_isZero_357_ == 1)
{
lean_dec(v_x_354_);
return v_x_355_;
}
else
{
lean_object* v_fst_358_; lean_object* v_snd_359_; lean_object* v___x_360_; lean_object* v_fst_361_; lean_object* v_snd_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_376_; 
v_fst_358_ = lean_ctor_get(v_x_355_, 0);
lean_inc(v_fst_358_);
v_snd_359_ = lean_ctor_get(v_x_355_, 1);
lean_inc(v_snd_359_);
lean_dec_ref(v_x_355_);
v___x_360_ = l_stdNext(v_snd_359_);
v_fst_361_ = lean_ctor_get(v___x_360_, 0);
v_snd_362_ = lean_ctor_get(v___x_360_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_376_ == 0)
{
v___x_364_ = v___x_360_;
v_isShared_365_ = v_isSharedCheck_376_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_snd_362_);
lean_inc(v_fst_361_);
lean_dec(v___x_360_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_376_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v_v_x27_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_366_ = lean_nat_mul(v_fst_358_, v_genMag_353_);
lean_dec(v_fst_358_);
v___x_367_ = lean_nat_sub(v_fst_361_, v_genLo_352_);
lean_dec(v_fst_361_);
v_v_x27_368_ = lean_nat_add(v___x_366_, v___x_367_);
lean_dec(v___x_367_);
lean_dec(v___x_366_);
v___x_369_ = lean_nat_div(v_x_354_, v_genMag_353_);
lean_dec(v_x_354_);
v___x_370_ = lean_unsigned_to_nat(1u);
v___x_371_ = lean_nat_sub(v___x_369_, v___x_370_);
lean_dec(v___x_369_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v_v_x27_368_);
v___x_373_ = v___x_364_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_v_x27_368_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_snd_362_);
v___x_373_ = v_reuseFailAlloc_375_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
v_x_354_ = v___x_371_;
v_x_355_ = v___x_373_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00IO_rand_spec__0_spec__0___boxed(lean_object* v_genLo_377_, lean_object* v_genMag_378_, lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00IO_rand_spec__0_spec__0(v_genLo_377_, v_genMag_378_, v_x_379_, v_x_380_);
lean_dec(v_genMag_378_);
lean_dec(v_genLo_377_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_randNat___at___00IO_rand_spec__0(lean_object* v_g_382_, lean_object* v_lo_383_, lean_object* v_hi_384_){
_start:
{
lean_object* v___y_386_; lean_object* v___y_387_; uint8_t v___x_412_; lean_object* v___y_414_; 
v___x_412_ = lean_nat_dec_lt(v_hi_384_, v_lo_383_);
if (v___x_412_ == 0)
{
v___y_414_ = v_lo_383_;
goto v___jp_413_;
}
else
{
v___y_414_ = v_hi_384_;
goto v___jp_413_;
}
v___jp_385_:
{
lean_object* v___x_388_; lean_object* v_fst_389_; lean_object* v_snd_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v_genMag_393_; lean_object* v_q_394_; lean_object* v___x_395_; lean_object* v_k_396_; lean_object* v_tgtMag_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_fst_401_; lean_object* v_snd_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_411_; 
v___x_388_ = ((lean_object*)(l_stdRange));
v_fst_389_ = lean_ctor_get(v___x_388_, 0);
v_snd_390_ = lean_ctor_get(v___x_388_, 1);
v___x_391_ = lean_nat_sub(v_snd_390_, v_fst_389_);
v___x_392_ = lean_unsigned_to_nat(1u);
v_genMag_393_ = lean_nat_add(v___x_391_, v___x_392_);
lean_dec(v___x_391_);
v_q_394_ = lean_unsigned_to_nat(1000u);
v___x_395_ = lean_nat_sub(v___y_387_, v___y_386_);
v_k_396_ = lean_nat_add(v___x_395_, v___x_392_);
lean_dec(v___x_395_);
v_tgtMag_397_ = lean_nat_mul(v_k_396_, v_q_394_);
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v_g_382_);
v___x_400_ = l___private_Init_Data_Random_0__randNatAux___at___00randNat___at___00IO_rand_spec__0_spec__0(v_fst_389_, v_genMag_393_, v_tgtMag_397_, v___x_399_);
lean_dec(v_genMag_393_);
v_fst_401_ = lean_ctor_get(v___x_400_, 0);
v_snd_402_ = lean_ctor_get(v___x_400_, 1);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_411_ == 0)
{
v___x_404_ = v___x_400_;
v_isShared_405_ = v_isSharedCheck_411_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_snd_402_);
lean_inc(v_fst_401_);
lean_dec(v___x_400_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_411_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v_v_x27_407_; lean_object* v___x_409_; 
v___x_406_ = lean_nat_mod(v_fst_401_, v_k_396_);
lean_dec(v_k_396_);
lean_dec(v_fst_401_);
v_v_x27_407_ = lean_nat_add(v___y_386_, v___x_406_);
lean_dec(v___x_406_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v_v_x27_407_);
v___x_409_ = v___x_404_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_v_x27_407_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_snd_402_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
v___jp_413_:
{
if (v___x_412_ == 0)
{
v___y_386_ = v___y_414_;
v___y_387_ = v_hi_384_;
goto v___jp_385_;
}
else
{
v___y_386_ = v___y_414_;
v___y_387_ = v_lo_383_;
goto v___jp_385_;
}
}
}
}
LEAN_EXPORT lean_object* l_randNat___at___00IO_rand_spec__0___boxed(lean_object* v_g_415_, lean_object* v_lo_416_, lean_object* v_hi_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_randNat___at___00IO_rand_spec__0(v_g_415_, v_lo_416_, v_hi_417_);
lean_dec(v_hi_417_);
lean_dec(v_lo_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_IO_rand(lean_object* v_lo_419_, lean_object* v_hi_420_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v_fst_425_; lean_object* v_snd_426_; lean_object* v___x_427_; 
v___x_422_ = l_IO_stdGenRef;
v___x_423_ = lean_st_ref_get(v___x_422_);
v___x_424_ = l_randNat___at___00IO_rand_spec__0(v___x_423_, v_lo_419_, v_hi_420_);
v_fst_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_fst_425_);
v_snd_426_ = lean_ctor_get(v___x_424_, 1);
lean_inc(v_snd_426_);
lean_dec_ref(v___x_424_);
v___x_427_ = lean_st_ref_set(v___x_422_, v_snd_426_);
return v_fst_425_;
}
}
LEAN_EXPORT lean_object* l_IO_rand___boxed(lean_object* v_lo_428_, lean_object* v_hi_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_IO_rand(v_lo_428_, v_hi_429_);
lean_dec(v_hi_429_);
lean_dec(v_lo_428_);
return v_res_431_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Extra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Random(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instInhabitedStdGen = _init_l_instInhabitedStdGen();
lean_mark_persistent(l_instInhabitedStdGen);
res = l___private_Init_Data_Random_0__initFn_00___x40_Init_Data_Random_2456098205____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_IO_stdGenRef = lean_io_result_get_value(res);
lean_mark_persistent(l_IO_stdGenRef);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Random(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray_Extra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Random(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Random(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Random(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Random(builtin);
}
#ifdef __cplusplus
}
#endif
