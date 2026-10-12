// Lean compiler output
// Module: Std.Sat.CNF.RelabelFin
// Imports: public import Init.Data.Nat.Order public import Std.Sat.CNF.Relabel import Init.Data.Option.Lemmas import Init.Omega import Init.Data.List.Impl import Init.Data.List.MinMax public import Init.Data.Array.MinMax import Init.TacticsExtra
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
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_Sat_CNF_relabel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_maxLiteral(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_maxLiteral___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_maxLiteral(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_maxLiteral___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_numLiterals(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_numLiterals___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Sat_CNF_relabelFin___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Sat_CNF_relabelFin___closed__0;
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0_spec__1(lean_object* v_as_1_, size_t v_i_2_, size_t v_stop_3_, lean_object* v_b_4_){
_start:
{
lean_object* v___y_6_; uint8_t v___x_10_; 
v___x_10_ = lean_usize_dec_eq(v_i_2_, v_stop_3_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = lean_array_uget_borrowed(v_as_1_, v_i_2_);
v___x_12_ = lean_nat_dec_le(v_b_4_, v___x_11_);
if (v___x_12_ == 0)
{
v___y_6_ = v_b_4_;
goto v___jp_5_;
}
else
{
v___y_6_ = v___x_11_;
goto v___jp_5_;
}
}
else
{
lean_inc(v_b_4_);
return v_b_4_;
}
v___jp_5_:
{
size_t v___x_7_; size_t v___x_8_; 
v___x_7_ = ((size_t)1ULL);
v___x_8_ = lean_usize_add(v_i_2_, v___x_7_);
v_i_2_ = v___x_8_;
v_b_4_ = v___y_6_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1_ = stack[0].m_obj;
size_t v_i_2_ = stack[1].m_num;
size_t v_stop_3_ = stack[2].m_num;
lean_object* v_b_4_ = stack[3].m_obj;
lean_object* v_res_13_;
v_res_13_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0_spec__1(v_as_1_, v_i_2_, v_stop_3_, v_b_4_);
stack->m_obj
 = v_res_13_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0_spec__1___boxed(lean_object* v_as_14_, lean_object* v_i_15_, lean_object* v_stop_16_, lean_object* v_b_17_){
_start:
{
size_t v_i_boxed_18_; size_t v_stop_boxed_19_; lean_object* v_res_20_; 
v_i_boxed_18_ = lean_unbox_usize(v_i_15_);
lean_dec(v_i_15_);
v_stop_boxed_19_ = lean_unbox_usize(v_stop_16_);
lean_dec(v_stop_16_);
v_res_20_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0_spec__1(v_as_14_, v_i_boxed_18_, v_stop_boxed_19_, v_b_17_);
lean_dec(v_b_17_);
lean_dec_ref(v_as_14_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0___redArg(lean_object* v_arr_21_){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_22_ = lean_unsigned_to_nat(0u);
v___x_23_ = lean_array_fget_borrowed(v_arr_21_, v___x_22_);
v___x_24_ = lean_unsigned_to_nat(1u);
v___x_25_ = lean_array_get_size(v_arr_21_);
v___x_26_ = lean_nat_dec_lt(v___x_24_, v___x_25_);
if (v___x_26_ == 0)
{
lean_inc(v___x_23_);
return v___x_23_;
}
else
{
size_t v___x_27_; size_t v___x_28_; lean_object* v___x_29_; 
v___x_27_ = ((size_t)1ULL);
v___x_28_ = lean_usize_of_nat(v___x_25_);
v___x_29_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0_spec__1(v_arr_21_, v___x_27_, v___x_28_, v___x_23_);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0___redArg___boxed(lean_object* v_arr_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0___redArg(v_arr_30_);
lean_dec_ref(v_arr_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0(lean_object* v_arr_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; uint8_t v___x_35_; 
v___x_33_ = lean_array_get_size(v_arr_32_);
v___x_34_ = lean_unsigned_to_nat(0u);
v___x_35_ = lean_nat_dec_eq(v___x_33_, v___x_34_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0___redArg(v_arr_32_);
v___x_37_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
return v___x_37_;
}
else
{
lean_object* v___x_38_; 
v___x_38_ = lean_box(0);
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* l_Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0___boxed(lean_object* v_arr_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0(v_arr_39_);
lean_dec_ref(v_arr_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_maxLiteral(lean_object* v_c_41_){
_start:
{
lean_object* v_atoms_42_; lean_object* v___x_43_; 
v_atoms_42_ = lean_ctor_get(v_c_41_, 0);
v___x_43_ = l_Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0(v_atoms_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_maxLiteral___boxed(lean_object* v_c_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Std_Sat_CNF_Clause_maxLiteral(v_c_44_);
lean_dec_ref(v_c_44_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0(lean_object* v_arr_46_, lean_object* v_h_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0___redArg(v_arr_46_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0___boxed(lean_object* v_arr_49_, lean_object* v_h_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Array_max___at___00Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0_spec__0(v_arr_49_, v_h_50_);
lean_dec_ref(v_arr_49_);
return v_res_51_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(lean_object* v_as_52_, size_t v_i_53_, size_t v_stop_54_, lean_object* v_b_55_){
_start:
{
lean_object* v___y_57_; uint8_t v___x_61_; 
v___x_61_ = lean_usize_dec_eq(v_i_53_, v_stop_54_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_array_uget_borrowed(v_as_52_, v_i_53_);
v___x_63_ = l_Std_Sat_CNF_Clause_maxLiteral(v___x_62_);
if (lean_obj_tag(v___x_63_) == 0)
{
v___y_57_ = v_b_55_;
goto v___jp_56_;
}
else
{
lean_object* v_val_64_; lean_object* v___x_65_; 
v_val_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_val_64_);
lean_dec_ref_known(v___x_63_, 1);
v___x_65_ = lean_array_push(v_b_55_, v_val_64_);
v___y_57_ = v___x_65_;
goto v___jp_56_;
}
}
else
{
return v_b_55_;
}
v___jp_56_:
{
size_t v___x_58_; size_t v___x_59_; 
v___x_58_ = ((size_t)1ULL);
v___x_59_ = lean_usize_add(v_i_53_, v___x_58_);
v_i_53_ = v___x_59_;
v_b_55_ = v___y_57_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_52_ = stack[0].m_obj;
size_t v_i_53_ = stack[1].m_num;
size_t v_stop_54_ = stack[2].m_num;
lean_object* v_b_55_ = stack[3].m_obj;
lean_object* v_res_66_;
v_res_66_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(v_as_52_, v_i_53_, v_stop_54_, v_b_55_);
stack->m_obj
 = v_res_66_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0___boxed(lean_object* v_as_67_, lean_object* v_i_68_, lean_object* v_stop_69_, lean_object* v_b_70_){
_start:
{
size_t v_i_boxed_71_; size_t v_stop_boxed_72_; lean_object* v_res_73_; 
v_i_boxed_71_ = lean_unbox_usize(v_i_68_);
lean_dec(v_i_68_);
v_stop_boxed_72_ = lean_unbox_usize(v_stop_69_);
lean_dec(v_stop_69_);
v_res_73_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(v_as_67_, v_i_boxed_71_, v_stop_boxed_72_, v_b_70_);
lean_dec_ref(v_as_67_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0(lean_object* v_as_76_, lean_object* v_start_77_, lean_object* v_stop_78_){
_start:
{
lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0));
v___x_80_ = lean_nat_dec_lt(v_start_77_, v_stop_78_);
if (v___x_80_ == 0)
{
return v___x_79_;
}
else
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = lean_array_get_size(v_as_76_);
v___x_82_ = lean_nat_dec_le(v_stop_78_, v___x_81_);
if (v___x_82_ == 0)
{
uint8_t v___x_83_; 
v___x_83_ = lean_nat_dec_lt(v_start_77_, v___x_81_);
if (v___x_83_ == 0)
{
return v___x_79_;
}
else
{
size_t v___x_84_; size_t v___x_85_; lean_object* v___x_86_; 
v___x_84_ = lean_usize_of_nat(v_start_77_);
v___x_85_ = lean_usize_of_nat(v___x_81_);
v___x_86_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(v_as_76_, v___x_84_, v___x_85_, v___x_79_);
return v___x_86_;
}
}
else
{
size_t v___x_87_; size_t v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_usize_of_nat(v_start_77_);
v___x_88_ = lean_usize_of_nat(v_stop_78_);
v___x_89_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0_spec__0(v_as_76_, v___x_87_, v___x_88_, v___x_79_);
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___boxed(lean_object* v_as_90_, lean_object* v_start_91_, lean_object* v_stop_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0(v_as_90_, v_start_91_, v_stop_92_);
lean_dec(v_stop_92_);
lean_dec(v_start_91_);
lean_dec_ref(v_as_90_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_maxLiteral(lean_object* v_f_94_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_95_ = lean_unsigned_to_nat(0u);
v___x_96_ = lean_array_get_size(v_f_94_);
v___x_97_ = l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0(v_f_94_, v___x_95_, v___x_96_);
v___x_98_ = l_Array_max_x3f___at___00Std_Sat_CNF_Clause_maxLiteral_spec__0(v___x_97_);
lean_dec_ref(v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_maxLiteral___boxed(lean_object* v_f_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_Sat_CNF_maxLiteral(v_f_99_);
lean_dec_ref(v_f_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_numLiterals(lean_object* v_f_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Std_Sat_CNF_maxLiteral(v_f_101_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v___x_103_; 
v___x_103_ = lean_unsigned_to_nat(0u);
return v___x_103_;
}
else
{
lean_object* v_val_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v_val_104_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_val_104_);
lean_dec_ref_known(v___x_102_, 1);
v___x_105_ = lean_unsigned_to_nat(1u);
v___x_106_ = lean_nat_add(v_val_104_, v___x_105_);
lean_dec(v_val_104_);
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_numLiterals___boxed(lean_object* v_f_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_Sat_CNF_numLiterals(v_f_107_);
lean_dec_ref(v_f_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter___redArg(lean_object* v_x_109_, lean_object* v_h__1_110_, lean_object* v_h__2_111_){
_start:
{
if (lean_obj_tag(v_x_109_) == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_dec(v_h__2_111_);
v___x_112_ = lean_box(0);
v___x_113_ = lean_apply_1(v_h__1_110_, v___x_112_);
return v___x_113_;
}
else
{
lean_object* v_val_114_; lean_object* v___x_115_; 
lean_dec(v_h__1_110_);
v_val_114_ = lean_ctor_get(v_x_109_, 0);
lean_inc(v_val_114_);
lean_dec_ref_known(v_x_109_, 1);
v___x_115_ = lean_apply_1(v_h__2_111_, v_val_114_);
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter(lean_object* v_motive_116_, lean_object* v_x_117_, lean_object* v_h__1_118_, lean_object* v_h__2_119_){
_start:
{
if (lean_obj_tag(v_x_117_) == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; 
lean_dec(v_h__2_119_);
v___x_120_ = lean_box(0);
v___x_121_ = lean_apply_1(v_h__1_118_, v___x_120_);
return v___x_121_;
}
else
{
lean_object* v_val_122_; lean_object* v___x_123_; 
lean_dec(v_h__1_118_);
v_val_122_ = lean_ctor_get(v_x_117_, 0);
lean_inc(v_val_122_);
lean_dec_ref_known(v_x_117_, 1);
v___x_123_ = lean_apply_1(v_h__2_119_, v_val_122_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lam__0(lean_object* v_n_124_, lean_object* v_i_125_){
_start:
{
uint8_t v___x_126_; 
v___x_126_ = lean_nat_dec_lt(v_i_125_, v_n_124_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
v___x_127_ = lean_unsigned_to_nat(0u);
return v___x_127_;
}
else
{
lean_inc(v_i_125_);
return v_i_125_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lam__0___boxed(lean_object* v_n_128_, lean_object* v_i_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Std_Sat_CNF_relabelFin___lam__0(v_n_128_, v_i_129_);
lean_dec(v_i_129_);
lean_dec(v_n_128_);
return v_res_130_;
}
}
static lean_object* _init_l_Std_Sat_CNF_relabelFin___closed__0(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = l_ByteArray_empty;
v___x_132_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Sat_CNF_maxLiteral_spec__0___closed__0));
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___x_131_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin(lean_object* v_f_134_){
_start:
{
uint8_t v___x_135_; 
lean_inc_ref(v_f_134_);
v___x_135_ = l_Std_Sat_CNF_instDecidableExistsVarMemOfDecidableEq___redArg(v_f_134_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = lean_array_get_size(v_f_134_);
lean_dec_ref(v_f_134_);
v___x_137_ = lean_obj_once(&l_Std_Sat_CNF_relabelFin___closed__0, &l_Std_Sat_CNF_relabelFin___closed__0_once, _init_l_Std_Sat_CNF_relabelFin___closed__0);
v___x_138_ = lean_mk_array(v___x_136_, v___x_137_);
return v___x_138_;
}
else
{
lean_object* v_n_139_; lean_object* v___f_140_; lean_object* v___x_141_; 
v_n_139_ = l_Std_Sat_CNF_numLiterals(v_f_134_);
v___f_140_ = lean_alloc_closure((void*)(l_Std_Sat_CNF_relabelFin___lam__0___boxed), 2, 1);
lean_closure_set(v___f_140_, 0, v_n_139_);
v___x_141_ = l_Std_Sat_CNF_relabel___redArg(v___f_140_, v_f_134_);
return v___x_141_;
}
}
}
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_CNF_Relabel(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_CNF_RelabelFin(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Relabel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_CNF_RelabelFin(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* initialize_Std_Sat_CNF_Relabel(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin);
lean_object* initialize_Init_Data_List_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Array_MinMax(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF_RelabelFin(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Relabel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_RelabelFin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_CNF_RelabelFin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_CNF_RelabelFin(builtin);
}
#ifdef __cplusplus
}
#endif
