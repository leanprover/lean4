// Lean compiler output
// Module: LeanExport
// Imports: public import Init public meta import Init public import LeanExport.Basic public import LeanExport.Parse
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
lean_object* l_LeanExport_initState(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_LeanExport_dumpMetadata___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_LeanExport_dumpConstant(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeNameLit(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore_spec__0(lean_object*);
lean_object* l_Lean_findSysroot(lean_object*);
lean_object* l_Lean_initSearchPath(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Options_empty;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
lean_object* l_LeanExport_M_run___redArg(lean_object*, lean_object*);
lean_object* l_List_tail_x3f___redArg(lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
lean_object* l_Lean_SMap_toList___at___00__private_Lean_Elab_DocString_Builtin_0__Lean_Doc_getQualified_spec__1___redArg(lean_object*);
lean_object* l_List_mapTR_loop___at___00Lean_Environment_dbgFormatAsyncState_spec__4(lean_object*, lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
static lean_once_cell_t l_List_forIn_x27_loop___at___00main_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___closed__0;
static lean_once_cell_t l_List_forIn_x27_loop___at___00main_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_partition_loop___at___00main_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "--"};
static const lean_object* l_List_partition_loop___at___00main_spec__0___closed__0 = (const lean_object*)&l_List_partition_loop___at___00main_spec__0___closed__0_value;
static lean_once_cell_t l_List_partition_loop___at___00main_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_partition_loop___at___00main_spec__0___closed__1;
LEAN_EXPORT lean_object* l_List_partition_loop___at___00main_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00main_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_span_loop___at___00main_spec__1(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00main_spec__5(lean_object*, lean_object*);
static const lean_string_object l_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_main___closed__0 = (const lean_object*)&l_main___closed__0_value;
static const lean_ctor_object l_main___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_main___closed__1 = (const lean_object*)&l_main___closed__1_value;
static const lean_array_object l_main___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__2 = (const lean_object*)&l_main___closed__2_value;
LEAN_EXPORT lean_object* _lean_main(lean_object*);
LEAN_EXPORT lean_object* l_main___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_List_forIn_x27_loop___at___00main_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00main_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_List_forIn_x27_loop___at___00main_spec__3___redArg___closed__0, &l_List_forIn_x27_loop___at___00main_spec__3___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00main_spec__3___redArg___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg(lean_object* v_as_x27_7_, lean_object* v_b_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
if (lean_obj_tag(v_as_x27_7_) == 0)
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_12_, 0, v_b_8_);
lean_ctor_set(v___x_12_, 1, v___y_10_);
v___x_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
else
{
lean_object* v_head_14_; lean_object* v_tail_15_; lean_object* v_visitedNames_16_; lean_object* v_visitedLevels_17_; lean_object* v_visitedExprs_18_; lean_object* v_visitedConstants_19_; uint8_t v_exportMData_20_; uint8_t v_exportUnsafe_21_; uint8_t v_ignoreMissing_22_; lean_object* v_recursorMap_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_36_; 
v_head_14_ = lean_ctor_get(v_as_x27_7_, 0);
v_tail_15_ = lean_ctor_get(v_as_x27_7_, 1);
v_visitedNames_16_ = lean_ctor_get(v___y_10_, 0);
v_visitedLevels_17_ = lean_ctor_get(v___y_10_, 1);
v_visitedExprs_18_ = lean_ctor_get(v___y_10_, 2);
v_visitedConstants_19_ = lean_ctor_get(v___y_10_, 3);
v_exportMData_20_ = lean_ctor_get_uint8(v___y_10_, sizeof(void*)*6);
v_exportUnsafe_21_ = lean_ctor_get_uint8(v___y_10_, sizeof(void*)*6 + 1);
v_ignoreMissing_22_ = lean_ctor_get_uint8(v___y_10_, sizeof(void*)*6 + 2);
v_recursorMap_23_ = lean_ctor_get(v___y_10_, 5);
v_isSharedCheck_36_ = !lean_is_exclusive(v___y_10_);
if (v_isSharedCheck_36_ == 0)
{
lean_object* v_unused_37_; 
v_unused_37_ = lean_ctor_get(v___y_10_, 4);
lean_dec(v_unused_37_);
v___x_25_ = v___y_10_;
v_isShared_26_ = v_isSharedCheck_36_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_recursorMap_23_);
lean_inc(v_visitedConstants_19_);
lean_inc(v_visitedExprs_18_);
lean_inc(v_visitedLevels_17_);
lean_inc(v_visitedNames_16_);
lean_dec(v___y_10_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_36_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_27_; lean_object* v___x_29_; 
v___x_27_ = lean_obj_once(&l_List_forIn_x27_loop___at___00main_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00main_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00main_spec__3___redArg___closed__1);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 4, v___x_27_);
v___x_29_ = v___x_25_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_visitedNames_16_);
lean_ctor_set(v_reuseFailAlloc_35_, 1, v_visitedLevels_17_);
lean_ctor_set(v_reuseFailAlloc_35_, 2, v_visitedExprs_18_);
lean_ctor_set(v_reuseFailAlloc_35_, 3, v_visitedConstants_19_);
lean_ctor_set(v_reuseFailAlloc_35_, 4, v___x_27_);
lean_ctor_set(v_reuseFailAlloc_35_, 5, v_recursorMap_23_);
lean_ctor_set_uint8(v_reuseFailAlloc_35_, sizeof(void*)*6, v_exportMData_20_);
lean_ctor_set_uint8(v_reuseFailAlloc_35_, sizeof(void*)*6 + 1, v_exportUnsafe_21_);
lean_ctor_set_uint8(v_reuseFailAlloc_35_, sizeof(void*)*6 + 2, v_ignoreMissing_22_);
v___x_29_ = v_reuseFailAlloc_35_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
lean_object* v___x_30_; 
lean_inc(v_head_14_);
v___x_30_ = l_LeanExport_dumpConstant(v_head_14_, v___y_9_, v___x_29_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v_a_31_; lean_object* v_snd_32_; lean_object* v___x_33_; 
v_a_31_ = lean_ctor_get(v___x_30_, 0);
lean_inc(v_a_31_);
lean_dec_ref_known(v___x_30_, 1);
v_snd_32_ = lean_ctor_get(v_a_31_, 1);
lean_inc(v_snd_32_);
lean_dec(v_a_31_);
v___x_33_ = lean_box(0);
v_as_x27_7_ = v_tail_15_;
v_b_8_ = v___x_33_;
v___y_10_ = v_snd_32_;
goto _start;
}
else
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___redArg___boxed(lean_object* v_as_x27_38_, lean_object* v_b_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v_as_x27_38_, v_b_39_, v___y_40_, v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v_as_x27_38_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_main___lam__0(lean_object* v_a_44_, lean_object* v_fst_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_LeanExport_initState(v_a_44_, v_fst_45_, v___y_47_, v___y_48_);
if (lean_obj_tag(v___x_50_) == 0)
{
lean_object* v_a_51_; lean_object* v_snd_52_; lean_object* v___x_53_; 
v_a_51_ = lean_ctor_get(v___x_50_, 0);
lean_inc(v_a_51_);
lean_dec_ref_known(v___x_50_, 1);
v_snd_52_ = lean_ctor_get(v_a_51_, 1);
lean_inc(v_snd_52_);
lean_dec(v_a_51_);
v___x_53_ = l_LeanExport_dumpMetadata___redArg(v_snd_52_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_a_54_; lean_object* v_snd_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
lean_inc(v_a_54_);
lean_dec_ref_known(v___x_53_, 1);
v_snd_55_ = lean_ctor_get(v_a_54_, 1);
lean_inc(v_snd_55_);
lean_dec(v_a_54_);
v___x_56_ = lean_box(0);
v___x_57_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v___y_46_, v___x_56_, v___y_47_, v_snd_55_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_74_; 
v_a_58_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_74_ == 0)
{
v___x_60_ = v___x_57_;
v_isShared_61_ = v_isSharedCheck_74_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_57_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_74_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v_snd_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_72_; 
v_snd_62_ = lean_ctor_get(v_a_58_, 1);
v_isSharedCheck_72_ = !lean_is_exclusive(v_a_58_);
if (v_isSharedCheck_72_ == 0)
{
lean_object* v_unused_73_; 
v_unused_73_ = lean_ctor_get(v_a_58_, 0);
lean_dec(v_unused_73_);
v___x_64_ = v_a_58_;
v_isShared_65_ = v_isSharedCheck_72_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_snd_62_);
lean_dec(v_a_58_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_72_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 0, v___x_56_);
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_56_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v_snd_62_);
v___x_67_ = v_reuseFailAlloc_71_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
lean_object* v___x_69_; 
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v___x_67_);
v___x_69_ = v___x_60_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_67_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
}
}
else
{
return v___x_57_;
}
}
else
{
return v___x_53_;
}
}
else
{
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object* v_a_75_, lean_object* v_fst_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_main___lam__0(v_a_75_, v_fst_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec(v_fst_76_);
return v_res_81_;
}
}
static lean_object* _init_l_List_partition_loop___at___00main_spec__0___closed__1(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = ((lean_object*)(l_List_partition_loop___at___00main_spec__0___closed__0));
v___x_84_ = lean_string_utf8_byte_size(v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00main_spec__0(lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
if (lean_obj_tag(v_a_85_) == 0)
{
lean_object* v_fst_87_; lean_object* v_snd_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_97_; 
v_fst_87_ = lean_ctor_get(v_a_86_, 0);
v_snd_88_ = lean_ctor_get(v_a_86_, 1);
v_isSharedCheck_97_ = !lean_is_exclusive(v_a_86_);
if (v_isSharedCheck_97_ == 0)
{
v___x_90_ = v_a_86_;
v_isShared_91_ = v_isSharedCheck_97_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_snd_88_);
lean_inc(v_fst_87_);
lean_dec(v_a_86_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_97_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_92_ = l_List_reverse___redArg(v_fst_87_);
v___x_93_ = l_List_reverse___redArg(v_snd_88_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 1, v___x_93_);
lean_ctor_set(v___x_90_, 0, v___x_92_);
v___x_95_ = v___x_90_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_92_);
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
else
{
lean_object* v_head_98_; lean_object* v_tail_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_131_; 
v_head_98_ = lean_ctor_get(v_a_85_, 0);
v_tail_99_ = lean_ctor_get(v_a_85_, 1);
v_isSharedCheck_131_ = !lean_is_exclusive(v_a_85_);
if (v_isSharedCheck_131_ == 0)
{
v___x_101_ = v_a_85_;
v_isShared_102_ = v_isSharedCheck_131_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_tail_99_);
lean_inc(v_head_98_);
lean_dec(v_a_85_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_131_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v_fst_103_; lean_object* v_snd_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_130_; 
v_fst_103_ = lean_ctor_get(v_a_86_, 0);
v_snd_104_ = lean_ctor_get(v_a_86_, 1);
v_isSharedCheck_130_ = !lean_is_exclusive(v_a_86_);
if (v_isSharedCheck_130_ == 0)
{
v___x_106_ = v_a_86_;
v_isShared_107_ = v_isSharedCheck_130_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_snd_104_);
lean_inc(v_fst_103_);
lean_dec(v_a_86_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_130_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
uint8_t v___y_117_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_121_ = ((lean_object*)(l_List_partition_loop___at___00main_spec__0___closed__0));
v___x_122_ = lean_string_utf8_byte_size(v_head_98_);
v___x_123_ = lean_obj_once(&l_List_partition_loop___at___00main_spec__0___closed__1, &l_List_partition_loop___at___00main_spec__0___closed__1_once, _init_l_List_partition_loop___at___00main_spec__0___closed__1);
v___x_124_ = lean_nat_dec_le(v___x_123_, v___x_122_);
if (v___x_124_ == 0)
{
goto v___jp_108_;
}
else
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_string_memcmp(v_head_98_, v___x_121_, v___x_125_, v___x_125_, v___x_123_);
if (v___x_126_ == 0)
{
v___y_117_ = v___x_126_;
goto v___jp_116_;
}
else
{
lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_127_ = lean_unsigned_to_nat(3u);
v___x_128_ = lean_string_length(v_head_98_);
v___x_129_ = lean_nat_dec_le(v___x_127_, v___x_128_);
v___y_117_ = v___x_129_;
goto v___jp_116_;
}
}
v___jp_108_:
{
lean_object* v___x_110_; 
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v_snd_104_);
v___x_110_ = v___x_101_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_head_98_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v_snd_104_);
v___x_110_ = v_reuseFailAlloc_115_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_112_; 
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 1, v___x_110_);
v___x_112_ = v___x_106_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_fst_103_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v___x_110_);
v___x_112_ = v_reuseFailAlloc_114_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
v_a_85_ = v_tail_99_;
v_a_86_ = v___x_112_;
goto _start;
}
}
}
v___jp_116_:
{
if (v___y_117_ == 0)
{
goto v___jp_108_;
}
else
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_del_object(v___x_106_);
lean_del_object(v___x_101_);
v___x_118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_118_, 0, v_head_98_);
lean_ctor_set(v___x_118_, 1, v_fst_103_);
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v_snd_104_);
v_a_85_ = v_tail_99_;
v_a_86_ = v___x_119_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00main_spec__4(lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
if (lean_obj_tag(v_a_132_) == 0)
{
lean_object* v___x_134_; 
v___x_134_ = l_List_reverse___redArg(v_a_133_);
return v___x_134_;
}
else
{
lean_object* v_head_135_; lean_object* v_tail_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_146_; 
v_head_135_ = lean_ctor_get(v_a_132_, 0);
v_tail_136_ = lean_ctor_get(v_a_132_, 1);
v_isSharedCheck_146_ = !lean_is_exclusive(v_a_132_);
if (v_isSharedCheck_146_ == 0)
{
v___x_138_ = v_a_132_;
v_isShared_139_ = v_isSharedCheck_146_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_tail_136_);
lean_inc(v_head_135_);
lean_dec(v_a_132_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_146_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
uint8_t v___x_140_; 
v___x_140_ = l_Lean_Name_isInternal(v_head_135_);
if (v___x_140_ == 0)
{
lean_object* v___x_142_; 
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 1, v_a_133_);
v___x_142_ = v___x_138_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_head_135_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_a_133_);
v___x_142_ = v_reuseFailAlloc_144_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
v_a_132_ = v_tail_136_;
v_a_133_ = v___x_142_;
goto _start;
}
}
else
{
lean_del_object(v___x_138_);
lean_dec(v_head_135_);
v_a_132_ = v_tail_136_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_span_loop___at___00main_spec__1(lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
if (lean_obj_tag(v_a_147_) == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = l_List_reverse___redArg(v_a_148_);
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v_a_147_);
return v___x_150_;
}
else
{
lean_object* v_head_151_; lean_object* v_tail_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v_head_151_ = lean_ctor_get(v_a_147_, 0);
v_tail_152_ = lean_ctor_get(v_a_147_, 1);
v___x_153_ = ((lean_object*)(l_List_partition_loop___at___00main_spec__0___closed__0));
v___x_154_ = lean_string_dec_eq(v_head_151_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_162_; 
lean_inc(v_tail_152_);
lean_inc(v_head_151_);
v_isSharedCheck_162_ = !lean_is_exclusive(v_a_147_);
if (v_isSharedCheck_162_ == 0)
{
lean_object* v_unused_163_; lean_object* v_unused_164_; 
v_unused_163_ = lean_ctor_get(v_a_147_, 1);
lean_dec(v_unused_163_);
v_unused_164_ = lean_ctor_get(v_a_147_, 0);
lean_dec(v_unused_164_);
v___x_156_ = v_a_147_;
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
else
{
lean_dec(v_a_147_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 1, v_a_148_);
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_head_151_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_a_148_);
v___x_159_ = v_reuseFailAlloc_161_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
v_a_147_ = v_tail_152_;
v_a_148_ = v___x_159_;
goto _start;
}
}
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = l_List_reverse___redArg(v_a_148_);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v_a_147_);
return v___x_166_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__4(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_171_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__3));
v___x_172_ = lean_unsigned_to_nat(14u);
v___x_173_ = lean_unsigned_to_nat(22u);
v___x_174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__2));
v___x_175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__1));
v___x_176_ = l_mkPanicMessageWithDecl(v___x_175_, v___x_174_, v___x_173_, v___x_172_, v___x_171_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2(size_t v_sz_177_, size_t v_i_178_, lean_object* v_bs_179_){
_start:
{
uint8_t v___x_180_; 
v___x_180_ = lean_usize_dec_lt(v_i_178_, v_sz_177_);
if (v___x_180_ == 0)
{
return v_bs_179_;
}
else
{
lean_object* v_v_181_; lean_object* v___x_182_; lean_object* v_bs_x27_183_; lean_object* v___y_185_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_v_181_ = lean_array_uget(v_bs_179_, v_i_178_);
v___x_182_ = lean_unsigned_to_nat(0u);
v_bs_x27_183_ = lean_array_uset(v_bs_179_, v_i_178_, v___x_182_);
v___x_192_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__0));
v___x_193_ = lean_string_append(v___x_192_, v_v_181_);
lean_dec(v_v_181_);
v___x_194_ = l_Lean_Syntax_decodeNameLit(v___x_193_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__4);
v___x_196_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore_spec__0(v___x_195_);
v___y_185_ = v___x_196_;
goto v___jp_184_;
}
else
{
lean_object* v_val_197_; 
v_val_197_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_val_197_);
lean_dec_ref_known(v___x_194_, 1);
v___y_185_ = v_val_197_;
goto v___jp_184_;
}
v___jp_184_:
{
uint8_t v___x_186_; lean_object* v___x_187_; size_t v___x_188_; size_t v___x_189_; lean_object* v___x_190_; 
v___x_186_ = 0;
v___x_187_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_187_, 0, v___y_185_);
lean_ctor_set_uint8(v___x_187_, sizeof(void*)*1, v___x_186_);
lean_ctor_set_uint8(v___x_187_, sizeof(void*)*1 + 1, v___x_180_);
lean_ctor_set_uint8(v___x_187_, sizeof(void*)*1 + 2, v___x_186_);
v___x_188_ = ((size_t)1ULL);
v___x_189_ = lean_usize_add(v_i_178_, v___x_188_);
v___x_190_ = lean_array_uset(v_bs_x27_183_, v_i_178_, v___x_187_);
v_i_178_ = v___x_189_;
v_bs_179_ = v___x_190_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___boxed(lean_object* v_sz_198_, lean_object* v_i_199_, lean_object* v_bs_200_){
_start:
{
size_t v_sz_boxed_201_; size_t v_i_boxed_202_; lean_object* v_res_203_; 
v_sz_boxed_201_ = lean_unbox_usize(v_sz_198_);
lean_dec(v_sz_198_);
v_i_boxed_202_ = lean_unbox_usize(v_i_199_);
lean_dec(v_i_199_);
v_res_203_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2(v_sz_boxed_201_, v_i_boxed_202_, v_bs_200_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00main_spec__5(lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
if (lean_obj_tag(v_a_204_) == 0)
{
lean_object* v___x_206_; 
v___x_206_ = l_List_reverse___redArg(v_a_205_);
return v___x_206_;
}
else
{
lean_object* v_head_207_; lean_object* v_tail_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_224_; 
v_head_207_ = lean_ctor_get(v_a_204_, 0);
v_tail_208_ = lean_ctor_get(v_a_204_, 1);
v_isSharedCheck_224_ = !lean_is_exclusive(v_a_204_);
if (v_isSharedCheck_224_ == 0)
{
v___x_210_ = v_a_204_;
v_isShared_211_ = v_isSharedCheck_224_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_tail_208_);
lean_inc(v_head_207_);
lean_dec(v_a_204_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_224_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___y_213_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__0));
v___x_219_ = lean_string_append(v___x_218_, v_head_207_);
lean_dec(v_head_207_);
v___x_220_ = l_Lean_Syntax_decodeNameLit(v___x_219_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___closed__4);
v___x_222_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore_spec__0(v___x_221_);
v___y_213_ = v___x_222_;
goto v___jp_212_;
}
else
{
lean_object* v_val_223_; 
v_val_223_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_val_223_);
lean_dec_ref_known(v___x_220_, 1);
v___y_213_ = v_val_223_;
goto v___jp_212_;
}
v___jp_212_:
{
lean_object* v___x_215_; 
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v_a_205_);
lean_ctor_set(v___x_210_, 0, v___y_213_);
v___x_215_ = v___x_210_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___y_213_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_a_205_);
v___x_215_ = v_reuseFailAlloc_217_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
v_a_204_ = v_tail_208_;
v_a_205_ = v___x_215_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_230_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = ((lean_object*)(l_main___closed__0));
v___x_233_ = l_Lean_findSysroot(v___x_232_);
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_a_234_);
lean_dec_ref_known(v___x_233_, 1);
v___x_235_ = lean_box(0);
v___x_236_ = l_Lean_initSearchPath(v_a_234_, v___x_235_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v_fst_239_; lean_object* v_snd_240_; lean_object* v___x_241_; lean_object* v_fst_242_; lean_object* v_snd_243_; lean_object* v___x_244_; size_t v_sz_245_; size_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint32_t v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; uint8_t v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec_ref_known(v___x_236_, 1);
v___x_237_ = ((lean_object*)(l_main___closed__1));
v___x_238_ = l_List_partition_loop___at___00main_spec__0(v_args_230_, v___x_237_);
v_fst_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_fst_239_);
v_snd_240_ = lean_ctor_get(v___x_238_, 1);
lean_inc(v_snd_240_);
lean_dec_ref(v___x_238_);
v___x_241_ = l_List_span_loop___at___00main_spec__1(v_snd_240_, v___x_235_);
v_fst_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_fst_242_);
v_snd_243_ = lean_ctor_get(v___x_241_, 1);
lean_inc(v_snd_243_);
lean_dec_ref(v___x_241_);
v___x_244_ = lean_array_mk(v_fst_242_);
v_sz_245_ = lean_array_size(v___x_244_);
v___x_246_ = ((size_t)0ULL);
v___x_247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2(v_sz_245_, v___x_246_, v___x_244_);
v___x_248_ = l_Lean_Options_empty;
v___x_249_ = 0;
v___x_250_ = ((lean_object*)(l_main___closed__2));
v___x_251_ = 0;
v___x_252_ = 2;
v___x_253_ = lean_box(1);
v___x_254_ = l_Lean_importModules(v___x_247_, v___x_248_, v___x_249_, v___x_250_, v___x_251_, v___x_251_, v___x_252_, v___x_253_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___y_257_; lean_object* v___x_260_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_255_);
lean_dec_ref_known(v___x_254_, 1);
v___x_260_ = l_List_tail_x3f___redArg(v_snd_243_);
lean_dec(v_snd_243_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
lean_inc(v_a_255_);
v___x_261_ = l_Lean_Environment_constants(v_a_255_);
v___x_262_ = l_Lean_SMap_toList___at___00__private_Lean_Elab_DocString_Builtin_0__Lean_Doc_getQualified_spec__1___redArg(v___x_261_);
lean_dec_ref(v___x_261_);
v___x_263_ = l_List_mapTR_loop___at___00Lean_Environment_dbgFormatAsyncState_spec__4(v___x_262_, v___x_235_);
v___x_264_ = l_List_filterTR_loop___at___00main_spec__4(v___x_263_, v___x_235_);
v___y_257_ = v___x_264_;
goto v___jp_256_;
}
else
{
lean_object* v_val_265_; lean_object* v___x_266_; 
v_val_265_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_val_265_);
lean_dec_ref_known(v___x_260_, 1);
v___x_266_ = l_List_mapTR_loop___at___00main_spec__5(v_val_265_, v___x_235_);
v___y_257_ = v___x_266_;
goto v___jp_256_;
}
v___jp_256_:
{
lean_object* v___f_258_; lean_object* v___x_259_; 
lean_inc(v_a_255_);
v___f_258_ = lean_alloc_closure((void*)(l_main___lam__0___boxed), 6, 3);
lean_closure_set(v___f_258_, 0, v_a_255_);
lean_closure_set(v___f_258_, 1, v_fst_239_);
lean_closure_set(v___f_258_, 2, v___y_257_);
v___x_259_ = l_LeanExport_M_run___redArg(v_a_255_, v___f_258_);
return v___x_259_;
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
lean_dec(v_snd_243_);
lean_dec(v_fst_239_);
v_a_267_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_254_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_254_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
else
{
lean_dec(v_args_230_);
return v___x_236_;
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
lean_dec(v_args_230_);
v_a_275_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_233_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_233_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = _lean_main(v_args_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3(lean_object* v_as_286_, lean_object* v_as_x27_287_, lean_object* v_b_288_, lean_object* v_a_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_List_forIn_x27_loop___at___00main_spec__3___redArg(v_as_x27_287_, v_b_288_, v___y_290_, v___y_291_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00main_spec__3___boxed(lean_object* v_as_294_, lean_object* v_as_x27_295_, lean_object* v_b_296_, lean_object* v_a_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_List_forIn_x27_loop___at___00main_spec__3(v_as_294_, v_as_x27_295_, v_b_296_, v_a_297_, v___y_298_, v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v_as_x27_295_);
lean_dec(v_as_294_);
return v_res_301_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_LeanExport_Basic(uint8_t builtin);
lean_object* initialize_LeanExport_Parse(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LeanExport(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanExport_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanExport_Parse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
char ** lean_setup_args(int argc, char ** argv);
#if defined(WIN32) || defined(_WIN32)
#include <windows.h>
#endif
lean_object* run_main(int argc, char ** argv) {
    lean_object* in = lean_box(0);
    int i = argc;
    while (i > 1) {
      lean_object* n;
      i--;
      n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);
      in = n;
    }
    return _lean_main(in);
}
int main(int argc, char ** argv) {
#if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  SetConsoleOutputCP(CP_UTF8);
#endif
  lean_object* res;
  argv = lean_setup_args(argc, argv);
  res = initialize_LeanExport(1 /* builtin */);
  lean_io_mark_end_initialization();
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
    lean_init_task_manager();
    res = lean_run_main(&run_main, argc, argv);
  }
  lean_finalize_task_manager();
  if (lean_io_result_is_ok(res)) {
    int ret = 0;
    lean_dec_ref(res);
    return ret;
  } else {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 1;
  }
}
#ifdef __cplusplus
}
#endif
