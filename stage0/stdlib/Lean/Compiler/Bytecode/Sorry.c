// Lean compiler output
// Module: Lean.Compiler.Bytecode.Sorry
// Imports: public import Lean.Compiler.Bytecode.Basic
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_find_bytecode_decl(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static const lean_string_object l_Lean_Compiler_Bytecode_Sorry_getSorryDepFor_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sorryAx"};
static const lean_object* l_Lean_Compiler_Bytecode_Sorry_getSorryDepFor_x3f___closed__0 = (const lean_object*)&l_Lean_Compiler_Bytecode_Sorry_getSorryDepFor_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_Bytecode_Sorry_getSorryDepFor_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_Bytecode_Sorry_getSorryDepFor_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 190, 164, 146, 38, 179, 69, 72)}};
static const lean_object* l_Lean_Compiler_Bytecode_Sorry_getSorryDepFor_x3f___closed__1 = (const lean_object*)&l_Lean_Compiler_Bytecode_Sorry_getSorryDepFor_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_Bytecode_Sorry_getSorryDepFor_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_Bytecode_Sorry_getSorryDepFor_x3f___closed__2 = (const lean_object*)&l_Lean_Compiler_Bytecode_Sorry_getSorryDepFor_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Sorry_getSorryDepFor_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Sorry_getSorryDepFor_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_Sorry_visitDecl_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_Sorry_visitDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Sorry_visitDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Sorry_visitDecl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_Sorry_collect_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_Sorry_collect_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Sorry_collect(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Sorry_collect___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_Bytecode_updateSorryDep_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_Bytecode_updateSorryDep_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_Bytecode_updateSorryDep___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_Bytecode_updateSorryDep___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_Bytecode_updateSorryDep___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_updateSorryDep___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_updateSorryDep___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_updateSorryDep(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_updateSorryDep___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Sorry_getSorryDepFor_x3f(lean_object* v_f_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v_g_10_; lean_object* v___y_11_; lean_object* v___y_19_; lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_22_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Sorry_getSorryDepFor_x3f___closed__1));
v___x_23_ = lean_name_eq(v_f_6_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v_localSorryMap_24_; lean_object* v___x_25_; 
v_localSorryMap_24_ = lean_ctor_get(v_a_8_, 0);
v___x_25_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_24_, v_f_6_);
if (lean_obj_tag(v___x_25_) == 1)
{
lean_object* v_val_26_; 
v_val_26_ = lean_ctor_get(v___x_25_, 0);
lean_inc(v_val_26_);
lean_dec_ref_known(v___x_25_, 1);
v_g_10_ = v_val_26_;
v___y_11_ = v_a_8_;
goto v___jp_9_;
}
else
{
lean_object* v___x_27_; 
lean_dec(v___x_25_);
lean_inc(v_f_6_);
lean_inc_ref(v_a_7_);
v___x_27_ = lean_find_bytecode_decl(v_a_7_, v_f_6_);
if (lean_obj_tag(v___x_27_) == 1)
{
lean_object* v_val_28_; lean_object* v_sorryDep_x3f_29_; 
v_val_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc(v_val_28_);
lean_dec_ref_known(v___x_27_, 1);
v_sorryDep_x3f_29_ = lean_ctor_get(v_val_28_, 8);
lean_inc(v_sorryDep_x3f_29_);
lean_dec(v_val_28_);
if (lean_obj_tag(v_sorryDep_x3f_29_) == 1)
{
lean_object* v_val_30_; 
v_val_30_ = lean_ctor_get(v_sorryDep_x3f_29_, 0);
lean_inc(v_val_30_);
lean_dec_ref_known(v_sorryDep_x3f_29_, 1);
v_g_10_ = v_val_30_;
v___y_11_ = v_a_8_;
goto v___jp_9_;
}
else
{
lean_dec(v_sorryDep_x3f_29_);
lean_dec(v_f_6_);
v___y_19_ = v_a_8_;
goto v___jp_18_;
}
}
else
{
lean_dec(v___x_27_);
lean_dec(v_f_6_);
v___y_19_ = v_a_8_;
goto v___jp_18_;
}
}
}
else
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_31_, 0, v_f_6_);
v___x_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v_a_8_);
return v___x_32_;
}
v___jp_9_:
{
lean_object* v___x_12_; uint8_t v___x_13_; 
v___x_12_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Sorry_getSorryDepFor_x3f___closed__1));
v___x_13_ = lean_name_eq(v_g_10_, v___x_12_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; lean_object* v___x_15_; 
lean_dec(v_f_6_);
v___x_14_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_14_, 0, v_g_10_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v___y_11_);
return v___x_15_;
}
else
{
lean_object* v___x_16_; lean_object* v___x_17_; 
lean_dec(v_g_10_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v_f_6_);
v___x_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v___y_11_);
return v___x_17_;
}
}
v___jp_18_:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = ((lean_object*)(l_Lean_Compiler_Bytecode_Sorry_getSorryDepFor_x3f___closed__2));
v___x_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
lean_ctor_set(v___x_21_, 1, v___y_19_);
return v___x_21_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Sorry_getSorryDepFor_x3f___boxed(lean_object* v_f_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Compiler_Bytecode_Sorry_getSorryDepFor_x3f(v_f_33_, v_a_34_, v_a_35_);
lean_dec_ref(v_a_34_);
return v_res_36_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_Sorry_visitDecl_spec__0(lean_object* v_as_37_, size_t v_i_38_, size_t v_stop_39_, lean_object* v_b_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
uint8_t v___x_43_; 
v___x_43_ = lean_usize_dec_eq(v_i_38_, v_stop_39_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v_fst_46_; 
v___x_44_ = lean_array_uget_borrowed(v_as_37_, v_i_38_);
lean_inc(v___x_44_);
v___x_45_ = l_Lean_Compiler_Bytecode_Sorry_getSorryDepFor_x3f(v___x_44_, v___y_41_, v___y_42_);
v_fst_46_ = lean_ctor_get(v___x_45_, 0);
if (lean_obj_tag(v_fst_46_) == 0)
{
return v___x_45_;
}
else
{
lean_object* v_snd_47_; lean_object* v_a_48_; size_t v___x_49_; size_t v___x_50_; 
lean_inc_ref(v_fst_46_);
v_snd_47_ = lean_ctor_get(v___x_45_, 1);
lean_inc(v_snd_47_);
lean_dec_ref(v___x_45_);
v_a_48_ = lean_ctor_get(v_fst_46_, 0);
lean_inc(v_a_48_);
lean_dec_ref_known(v_fst_46_, 1);
v___x_49_ = ((size_t)1ULL);
v___x_50_ = lean_usize_add(v_i_38_, v___x_49_);
v_i_38_ = v___x_50_;
v_b_40_ = v_a_48_;
v___y_42_ = v_snd_47_;
goto _start;
}
}
else
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_52_, 0, v_b_40_);
v___x_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v___y_42_);
return v___x_53_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_Sorry_visitDecl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_37_ = stack[0].m_obj;
size_t v_i_38_ = stack[1].m_num;
size_t v_stop_39_ = stack[2].m_num;
lean_object* v_b_40_ = stack[3].m_obj;
lean_object* v___y_41_ = stack[4].m_obj;
lean_object* v___y_42_ = stack[5].m_obj;
lean_object* v_res_54_;
v_res_54_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_Sorry_visitDecl_spec__0(v_as_37_, v_i_38_, v_stop_39_, v_b_40_, v___y_41_, v___y_42_);
stack->m_obj
 = v_res_54_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_Sorry_visitDecl_spec__0___boxed(lean_object* v_as_55_, lean_object* v_i_56_, lean_object* v_stop_57_, lean_object* v_b_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
size_t v_i_boxed_61_; size_t v_stop_boxed_62_; lean_object* v_res_63_; 
v_i_boxed_61_ = lean_unbox_usize(v_i_56_);
lean_dec(v_i_56_);
v_stop_boxed_62_ = lean_unbox_usize(v_stop_57_);
lean_dec(v_stop_57_);
v_res_63_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_Sorry_visitDecl_spec__0(v_as_55_, v_i_boxed_61_, v_stop_boxed_62_, v_b_58_, v___y_59_, v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec_ref(v_as_55_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Sorry_visitDecl(lean_object* v_d_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_snd_68_; lean_object* v_localSorryMap_71_; lean_object* v_name_72_; lean_object* v_symbols_73_; uint8_t v___x_74_; 
v_localSorryMap_71_ = lean_ctor_get(v_a_66_, 0);
v_name_72_ = lean_ctor_get(v_d_64_, 0);
lean_inc(v_name_72_);
v_symbols_73_ = lean_ctor_get(v_d_64_, 4);
lean_inc_ref(v_symbols_73_);
lean_dec_ref(v_d_64_);
v___x_74_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_name_72_, v_localSorryMap_71_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; lean_object* v___y_79_; 
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = lean_array_get_size(v_symbols_73_);
v___x_77_ = lean_nat_dec_lt(v___x_75_, v___x_76_);
if (v___x_77_ == 0)
{
lean_dec_ref(v_symbols_73_);
lean_dec(v_name_72_);
v_snd_68_ = v_a_66_;
goto v___jp_67_;
}
else
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_box(0);
v___x_103_ = lean_nat_dec_le(v___x_76_, v___x_76_);
if (v___x_103_ == 0)
{
if (v___x_77_ == 0)
{
lean_dec_ref(v_symbols_73_);
lean_dec(v_name_72_);
v_snd_68_ = v_a_66_;
goto v___jp_67_;
}
else
{
size_t v___x_104_; size_t v___x_105_; lean_object* v___x_106_; 
v___x_104_ = ((size_t)0ULL);
v___x_105_ = lean_usize_of_nat(v___x_76_);
v___x_106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_Sorry_visitDecl_spec__0(v_symbols_73_, v___x_104_, v___x_105_, v___x_102_, v_a_65_, v_a_66_);
lean_dec_ref(v_symbols_73_);
v___y_79_ = v___x_106_;
goto v___jp_78_;
}
}
else
{
size_t v___x_107_; size_t v___x_108_; lean_object* v___x_109_; 
v___x_107_ = ((size_t)0ULL);
v___x_108_ = lean_usize_of_nat(v___x_76_);
v___x_109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_Sorry_visitDecl_spec__0(v_symbols_73_, v___x_107_, v___x_108_, v___x_102_, v_a_65_, v_a_66_);
lean_dec_ref(v_symbols_73_);
v___y_79_ = v___x_109_;
goto v___jp_78_;
}
}
v___jp_78_:
{
lean_object* v_fst_80_; 
v_fst_80_ = lean_ctor_get(v___y_79_, 0);
if (lean_obj_tag(v_fst_80_) == 0)
{
lean_object* v_snd_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_99_; 
lean_inc_ref(v_fst_80_);
v_snd_81_ = lean_ctor_get(v___y_79_, 1);
v_isSharedCheck_99_ = !lean_is_exclusive(v___y_79_);
if (v_isSharedCheck_99_ == 0)
{
lean_object* v_unused_100_; 
v_unused_100_ = lean_ctor_get(v___y_79_, 0);
lean_dec(v_unused_100_);
v___x_83_ = v___y_79_;
v_isShared_84_ = v_isSharedCheck_99_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_snd_81_);
lean_dec(v___y_79_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_99_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v_a_85_; lean_object* v_localSorryMap_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_98_; 
v_a_85_ = lean_ctor_get(v_fst_80_, 0);
lean_inc(v_a_85_);
lean_dec_ref_known(v_fst_80_, 1);
v_localSorryMap_86_ = lean_ctor_get(v_snd_81_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v_snd_81_);
if (v_isSharedCheck_98_ == 0)
{
v___x_88_ = v_snd_81_;
v_isShared_89_ = v_isSharedCheck_98_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_localSorryMap_86_);
lean_dec(v_snd_81_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_98_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_90_ = lean_box(0);
v___x_91_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_72_, v_a_85_, v_localSorryMap_86_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 0, v___x_91_);
v___x_93_ = v___x_88_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v___x_91_);
v___x_93_ = v_reuseFailAlloc_97_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_95_; 
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*1, v___x_77_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 1, v___x_93_);
lean_ctor_set(v___x_83_, 0, v___x_90_);
v___x_95_ = v___x_83_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_90_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
}
else
{
lean_object* v_snd_101_; 
lean_dec(v_name_72_);
v_snd_101_ = lean_ctor_get(v___y_79_, 1);
lean_inc(v_snd_101_);
lean_dec_ref(v___y_79_);
v_snd_68_ = v_snd_101_;
goto v___jp_67_;
}
}
}
else
{
lean_object* v___x_110_; lean_object* v___x_111_; 
lean_dec_ref(v_symbols_73_);
lean_dec(v_name_72_);
v___x_110_ = lean_box(0);
v___x_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v_a_66_);
return v___x_111_;
}
v___jp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_box(0);
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v_snd_68_);
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Sorry_visitDecl___boxed(lean_object* v_d_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Compiler_Bytecode_Sorry_visitDecl(v_d_112_, v_a_113_, v_a_114_);
lean_dec_ref(v_a_113_);
return v_res_115_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_Sorry_collect_spec__0(lean_object* v_as_116_, size_t v_i_117_, size_t v_stop_118_, lean_object* v_b_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
uint8_t v___x_122_; 
v___x_122_ = lean_usize_dec_eq(v_i_117_, v_stop_118_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_fst_125_; lean_object* v_snd_126_; size_t v___x_127_; size_t v___x_128_; 
v___x_123_ = lean_array_uget_borrowed(v_as_116_, v_i_117_);
lean_inc(v___x_123_);
v___x_124_ = l_Lean_Compiler_Bytecode_Sorry_visitDecl(v___x_123_, v___y_120_, v___y_121_);
v_fst_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_fst_125_);
v_snd_126_ = lean_ctor_get(v___x_124_, 1);
lean_inc(v_snd_126_);
lean_dec_ref(v___x_124_);
v___x_127_ = ((size_t)1ULL);
v___x_128_ = lean_usize_add(v_i_117_, v___x_127_);
v_i_117_ = v___x_128_;
v_b_119_ = v_fst_125_;
v___y_121_ = v_snd_126_;
goto _start;
}
else
{
lean_object* v___x_130_; 
v___x_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_130_, 0, v_b_119_);
lean_ctor_set(v___x_130_, 1, v___y_121_);
return v___x_130_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_Sorry_collect_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_116_ = stack[0].m_obj;
size_t v_i_117_ = stack[1].m_num;
size_t v_stop_118_ = stack[2].m_num;
lean_object* v_b_119_ = stack[3].m_obj;
lean_object* v___y_120_ = stack[4].m_obj;
lean_object* v___y_121_ = stack[5].m_obj;
lean_object* v_res_131_;
v_res_131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_Sorry_collect_spec__0(v_as_116_, v_i_117_, v_stop_118_, v_b_119_, v___y_120_, v___y_121_);
stack->m_obj
 = v_res_131_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_Sorry_collect_spec__0___boxed(lean_object* v_as_132_, lean_object* v_i_133_, lean_object* v_stop_134_, lean_object* v_b_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
size_t v_i_boxed_138_; size_t v_stop_boxed_139_; lean_object* v_res_140_; 
v_i_boxed_138_ = lean_unbox_usize(v_i_133_);
lean_dec(v_i_133_);
v_stop_boxed_139_ = lean_unbox_usize(v_stop_134_);
lean_dec(v_stop_134_);
v_res_140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_Sorry_collect_spec__0(v_as_132_, v_i_boxed_138_, v_stop_boxed_139_, v_b_135_, v___y_136_, v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec_ref(v_as_132_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Sorry_collect(lean_object* v_decls_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_snd_145_; lean_object* v___y_149_; lean_object* v_localSorryMap_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_172_; 
v_localSorryMap_153_ = lean_ctor_get(v_a_143_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v_a_143_);
if (v_isSharedCheck_172_ == 0)
{
v___x_155_ = v_a_143_;
v_isShared_156_ = v_isSharedCheck_172_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_localSorryMap_153_);
lean_dec(v_a_143_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_172_;
goto v_resetjp_154_;
}
v___jp_144_:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_box(0);
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v_snd_145_);
return v___x_147_;
}
v___jp_148_:
{
lean_object* v_snd_150_; uint8_t v_modified_151_; 
v_snd_150_ = lean_ctor_get(v___y_149_, 1);
lean_inc(v_snd_150_);
lean_dec_ref(v___y_149_);
v_modified_151_ = lean_ctor_get_uint8(v_snd_150_, sizeof(void*)*1);
if (v_modified_151_ == 0)
{
v_snd_145_ = v_snd_150_;
goto v___jp_144_;
}
else
{
v_a_143_ = v_snd_150_;
goto _start;
}
}
v_resetjp_154_:
{
uint8_t v___x_157_; lean_object* v___x_159_; 
v___x_157_ = 0;
if (v_isShared_156_ == 0)
{
v___x_159_ = v___x_155_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_localSorryMap_153_);
v___x_159_ = v_reuseFailAlloc_171_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
lean_ctor_set_uint8(v___x_159_, sizeof(void*)*1, v___x_157_);
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = lean_array_get_size(v_decls_141_);
v___x_162_ = lean_nat_dec_lt(v___x_160_, v___x_161_);
if (v___x_162_ == 0)
{
v_snd_145_ = v___x_159_;
goto v___jp_144_;
}
else
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_box(0);
v___x_164_ = lean_nat_dec_le(v___x_161_, v___x_161_);
if (v___x_164_ == 0)
{
if (v___x_162_ == 0)
{
v_snd_145_ = v___x_159_;
goto v___jp_144_;
}
else
{
size_t v___x_165_; size_t v___x_166_; lean_object* v___x_167_; 
v___x_165_ = ((size_t)0ULL);
v___x_166_ = lean_usize_of_nat(v___x_161_);
v___x_167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_Sorry_collect_spec__0(v_decls_141_, v___x_165_, v___x_166_, v___x_163_, v_a_142_, v___x_159_);
v___y_149_ = v___x_167_;
goto v___jp_148_;
}
}
else
{
size_t v___x_168_; size_t v___x_169_; lean_object* v___x_170_; 
v___x_168_ = ((size_t)0ULL);
v___x_169_ = lean_usize_of_nat(v___x_161_);
v___x_170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_Bytecode_Sorry_collect_spec__0(v_decls_141_, v___x_168_, v___x_169_, v___x_163_, v_a_142_, v___x_159_);
v___y_149_ = v___x_170_;
goto v___jp_148_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_Sorry_collect___boxed(lean_object* v_decls_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_Compiler_Bytecode_Sorry_collect(v_decls_173_, v_a_174_, v_a_175_);
lean_dec_ref(v_a_174_);
lean_dec_ref(v_decls_173_);
return v_res_176_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_Bytecode_updateSorryDep_spec__0(lean_object* v_snd_177_, size_t v_sz_178_, size_t v_i_179_, lean_object* v_bs_180_){
_start:
{
uint8_t v___x_181_; 
v___x_181_ = lean_usize_dec_lt(v_i_179_, v_sz_178_);
if (v___x_181_ == 0)
{
return v_bs_180_;
}
else
{
lean_object* v_localSorryMap_182_; lean_object* v_v_183_; lean_object* v_name_184_; lean_object* v_code_185_; lean_object* v_stackReserved_186_; lean_object* v_stackSpace_187_; lean_object* v_symbols_188_; lean_object* v_cache_189_; lean_object* v_arity_190_; lean_object* v_constants_191_; lean_object* v___x_192_; lean_object* v_bs_x27_193_; lean_object* v___y_195_; lean_object* v___x_200_; 
v_localSorryMap_182_ = lean_ctor_get(v_snd_177_, 0);
v_v_183_ = lean_array_uget(v_bs_180_, v_i_179_);
v_name_184_ = lean_ctor_get(v_v_183_, 0);
v_code_185_ = lean_ctor_get(v_v_183_, 1);
v_stackReserved_186_ = lean_ctor_get(v_v_183_, 2);
v_stackSpace_187_ = lean_ctor_get(v_v_183_, 3);
v_symbols_188_ = lean_ctor_get(v_v_183_, 4);
v_cache_189_ = lean_ctor_get(v_v_183_, 5);
v_arity_190_ = lean_ctor_get(v_v_183_, 6);
v_constants_191_ = lean_ctor_get(v_v_183_, 7);
v___x_192_ = lean_unsigned_to_nat(0u);
v_bs_x27_193_ = lean_array_uset(v_bs_180_, v_i_179_, v___x_192_);
v___x_200_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_localSorryMap_182_, v_name_184_);
if (lean_obj_tag(v___x_200_) == 1)
{
lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_inc_ref(v_constants_191_);
lean_inc(v_arity_190_);
lean_inc(v_cache_189_);
lean_inc_ref(v_symbols_188_);
lean_inc(v_stackSpace_187_);
lean_inc(v_stackReserved_186_);
lean_inc_ref(v_code_185_);
lean_inc(v_name_184_);
v_isSharedCheck_207_ = !lean_is_exclusive(v_v_183_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; lean_object* v_unused_209_; lean_object* v_unused_210_; lean_object* v_unused_211_; lean_object* v_unused_212_; lean_object* v_unused_213_; lean_object* v_unused_214_; lean_object* v_unused_215_; lean_object* v_unused_216_; 
v_unused_208_ = lean_ctor_get(v_v_183_, 8);
lean_dec(v_unused_208_);
v_unused_209_ = lean_ctor_get(v_v_183_, 7);
lean_dec(v_unused_209_);
v_unused_210_ = lean_ctor_get(v_v_183_, 6);
lean_dec(v_unused_210_);
v_unused_211_ = lean_ctor_get(v_v_183_, 5);
lean_dec(v_unused_211_);
v_unused_212_ = lean_ctor_get(v_v_183_, 4);
lean_dec(v_unused_212_);
v_unused_213_ = lean_ctor_get(v_v_183_, 3);
lean_dec(v_unused_213_);
v_unused_214_ = lean_ctor_get(v_v_183_, 2);
lean_dec(v_unused_214_);
v_unused_215_ = lean_ctor_get(v_v_183_, 1);
lean_dec(v_unused_215_);
v_unused_216_ = lean_ctor_get(v_v_183_, 0);
lean_dec(v_unused_216_);
v___x_202_ = v_v_183_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_dec(v_v_183_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 8, v___x_200_);
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_name_184_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_code_185_);
lean_ctor_set(v_reuseFailAlloc_206_, 2, v_stackReserved_186_);
lean_ctor_set(v_reuseFailAlloc_206_, 3, v_stackSpace_187_);
lean_ctor_set(v_reuseFailAlloc_206_, 4, v_symbols_188_);
lean_ctor_set(v_reuseFailAlloc_206_, 5, v_cache_189_);
lean_ctor_set(v_reuseFailAlloc_206_, 6, v_arity_190_);
lean_ctor_set(v_reuseFailAlloc_206_, 7, v_constants_191_);
lean_ctor_set(v_reuseFailAlloc_206_, 8, v___x_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
v___y_195_ = v___x_205_;
goto v___jp_194_;
}
}
}
else
{
lean_dec(v___x_200_);
v___y_195_ = v_v_183_;
goto v___jp_194_;
}
v___jp_194_:
{
size_t v___x_196_; size_t v___x_197_; lean_object* v___x_198_; 
v___x_196_ = ((size_t)1ULL);
v___x_197_ = lean_usize_add(v_i_179_, v___x_196_);
v___x_198_ = lean_array_uset(v_bs_x27_193_, v_i_179_, v___y_195_);
v_i_179_ = v___x_197_;
v_bs_180_ = v___x_198_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_Bytecode_updateSorryDep_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_177_ = stack[0].m_obj;
size_t v_sz_178_ = stack[1].m_num;
size_t v_i_179_ = stack[2].m_num;
lean_object* v_bs_180_ = stack[3].m_obj;
lean_object* v_res_217_;
v_res_217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_Bytecode_updateSorryDep_spec__0(v_snd_177_, v_sz_178_, v_i_179_, v_bs_180_);
stack->m_obj
 = v_res_217_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_Bytecode_updateSorryDep_spec__0___boxed(lean_object* v_snd_218_, lean_object* v_sz_219_, lean_object* v_i_220_, lean_object* v_bs_221_){
_start:
{
size_t v_sz_boxed_222_; size_t v_i_boxed_223_; lean_object* v_res_224_; 
v_sz_boxed_222_ = lean_unbox_usize(v_sz_219_);
lean_dec(v_sz_219_);
v_i_boxed_223_ = lean_unbox_usize(v_i_220_);
lean_dec(v_i_220_);
v_res_224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_Bytecode_updateSorryDep_spec__0(v_snd_218_, v_sz_boxed_222_, v_i_boxed_223_, v_bs_221_);
lean_dec_ref(v_snd_218_);
return v_res_224_;
}
}
lean_object* l_Lean_Compiler_Bytecode_updateSorryDep___redArg(lean_object* v_decls_228_, lean_object* v_a_229_){
_start:
{
lean_object* v___x_231_; lean_object* v_env_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v_snd_235_; size_t v_sz_236_; size_t v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_231_ = lean_st_ref_get(v_a_229_);
v_env_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc_ref(v_env_232_);
lean_dec(v___x_231_);
v___x_233_ = ((lean_object*)(l_Lean_Compiler_Bytecode_updateSorryDep___redArg___closed__0));
v___x_234_ = l_Lean_Compiler_Bytecode_Sorry_collect(v_decls_228_, v_env_232_, v___x_233_);
lean_dec_ref(v_env_232_);
v_snd_235_ = lean_ctor_get(v___x_234_, 1);
lean_inc(v_snd_235_);
lean_dec_ref(v___x_234_);
v_sz_236_ = lean_array_size(v_decls_228_);
v___x_237_ = ((size_t)0ULL);
v___x_238_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_Bytecode_updateSorryDep_spec__0(v_snd_235_, v_sz_236_, v___x_237_, v_decls_228_);
lean_dec(v_snd_235_);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_updateSorryDep___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_228_ = stack[0].m_obj;
lean_object* v_a_229_ = stack[1].m_obj;
lean_object* v_res_240_;
v_res_240_ = l_Lean_Compiler_Bytecode_updateSorryDep___redArg(v_decls_228_, v_a_229_);
stack->m_obj
 = v_res_240_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_updateSorryDep___redArg___boxed(lean_object* v_decls_241_, lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Compiler_Bytecode_updateSorryDep___redArg(v_decls_241_, v_a_242_);
lean_dec(v_a_242_);
return v_res_244_;
}
}
lean_object* l_Lean_Compiler_Bytecode_updateSorryDep(lean_object* v_decls_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Lean_Compiler_Bytecode_updateSorryDep___redArg(v_decls_245_, v_a_247_);
return v___x_249_;
}
}
LEAN_EXPORT void l_Lean_Compiler_Bytecode_updateSorryDep_0interp(lean_interpreter_value* stack)
{
lean_object* v_decls_245_ = stack[0].m_obj;
lean_object* v_a_246_ = stack[1].m_obj;
lean_object* v_a_247_ = stack[2].m_obj;
lean_object* v_res_250_;
v_res_250_ = l_Lean_Compiler_Bytecode_updateSorryDep(v_decls_245_, v_a_246_, v_a_247_);
stack->m_obj
 = v_res_250_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_Bytecode_updateSorryDep___boxed(lean_object* v_decls_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Compiler_Bytecode_updateSorryDep(v_decls_251_, v_a_252_, v_a_253_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
return v_res_255_;
}
}
lean_object* runtime_initialize_Lean_Compiler_Bytecode_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_Bytecode_Sorry(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_Bytecode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_Bytecode_Sorry(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_Bytecode_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Bytecode_Sorry(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_Bytecode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Bytecode_Sorry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_Bytecode_Sorry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_Bytecode_Sorry(builtin);
}
#ifdef __cplusplus
}
#endif
