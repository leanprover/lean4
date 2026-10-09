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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeNameLit(lean_object*);
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
lean_object* l_List_tail_x3f___redArg(lean_object*);
lean_object* l_LeanExport_dumpEnv(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_partition_loop___at___00main_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "--"};
static const lean_object* l_List_partition_loop___at___00main_spec__0___closed__0 = (const lean_object*)&l_List_partition_loop___at___00main_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_partition_loop___at___00main_spec__0(lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00main_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_List_mapTR_loop___at___00main_spec__3___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00main_spec__3___closed__0_value;
static const lean_string_object l_List_mapTR_loop___at___00main_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_List_mapTR_loop___at___00main_spec__3___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00main_spec__3___closed__1_value;
static const lean_string_object l_List_mapTR_loop___at___00main_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_List_mapTR_loop___at___00main_spec__3___closed__2 = (const lean_object*)&l_List_mapTR_loop___at___00main_spec__3___closed__2_value;
static const lean_string_object l_List_mapTR_loop___at___00main_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_List_mapTR_loop___at___00main_spec__3___closed__3 = (const lean_object*)&l_List_mapTR_loop___at___00main_spec__3___closed__3_value;
static lean_once_cell_t l_List_mapTR_loop___at___00main_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00main_spec__3___closed__4;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00main_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_span_loop___at___00main_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_main___closed__0 = (const lean_object*)&l_main___closed__0_value;
static const lean_ctor_object l_main___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_main___closed__1 = (const lean_object*)&l_main___closed__1_value;
static const lean_array_object l_main___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___closed__2 = (const lean_object*)&l_main___closed__2_value;
LEAN_EXPORT lean_object* _lean_main(lean_object*);
LEAN_EXPORT lean_object* l_main___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partition_loop___at___00main_spec__0(lean_object* v_a_2_, lean_object* v_a_3_){
_start:
{
if (lean_obj_tag(v_a_2_) == 0)
{
lean_object* v_fst_4_; lean_object* v_snd_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_14_; 
v_fst_4_ = lean_ctor_get(v_a_3_, 0);
v_snd_5_ = lean_ctor_get(v_a_3_, 1);
v_isSharedCheck_14_ = !lean_is_exclusive(v_a_3_);
if (v_isSharedCheck_14_ == 0)
{
v___x_7_ = v_a_3_;
v_isShared_8_ = v_isSharedCheck_14_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_snd_5_);
lean_inc(v_fst_4_);
lean_dec(v_a_3_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_14_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_12_; 
v___x_9_ = l_List_reverse___redArg(v_fst_4_);
v___x_10_ = l_List_reverse___redArg(v_snd_5_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v___x_10_);
lean_ctor_set(v___x_7_, 0, v___x_9_);
v___x_12_ = v___x_7_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v___x_9_);
lean_ctor_set(v_reuseFailAlloc_13_, 1, v___x_10_);
v___x_12_ = v_reuseFailAlloc_13_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
return v___x_12_;
}
}
}
else
{
lean_object* v_head_15_; lean_object* v_tail_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_48_; 
v_head_15_ = lean_ctor_get(v_a_2_, 0);
v_tail_16_ = lean_ctor_get(v_a_2_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v_a_2_);
if (v_isSharedCheck_48_ == 0)
{
v___x_18_ = v_a_2_;
v_isShared_19_ = v_isSharedCheck_48_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_tail_16_);
lean_inc(v_head_15_);
lean_dec(v_a_2_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_48_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v_fst_20_; lean_object* v_snd_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_47_; 
v_fst_20_ = lean_ctor_get(v_a_3_, 0);
v_snd_21_ = lean_ctor_get(v_a_3_, 1);
v_isSharedCheck_47_ = !lean_is_exclusive(v_a_3_);
if (v_isSharedCheck_47_ == 0)
{
v___x_23_ = v_a_3_;
v_isShared_24_ = v_isSharedCheck_47_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_snd_21_);
lean_inc(v_fst_20_);
lean_dec(v_a_3_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_47_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
uint8_t v___y_34_; lean_object* v___x_38_; lean_object* v___x_39_; uint8_t v___x_40_; 
v___x_38_ = lean_string_utf8_byte_size(v_head_15_);
v___x_39_ = lean_unsigned_to_nat(2u);
v___x_40_ = lean_nat_dec_le(v___x_39_, v___x_38_);
if (v___x_40_ == 0)
{
goto v___jp_25_;
}
else
{
lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v___x_41_ = ((lean_object*)(l_List_partition_loop___at___00main_spec__0___closed__0));
v___x_42_ = lean_unsigned_to_nat(0u);
v___x_43_ = lean_string_memcmp(v_head_15_, v___x_41_, v___x_42_, v___x_42_, v___x_39_);
if (v___x_43_ == 0)
{
v___y_34_ = v___x_43_;
goto v___jp_33_;
}
else
{
lean_object* v___x_44_; lean_object* v___x_45_; uint8_t v___x_46_; 
v___x_44_ = lean_unsigned_to_nat(3u);
v___x_45_ = lean_string_length(v_head_15_);
v___x_46_ = lean_nat_dec_le(v___x_44_, v___x_45_);
v___y_34_ = v___x_46_;
goto v___jp_33_;
}
}
v___jp_25_:
{
lean_object* v___x_27_; 
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 1, v_snd_21_);
v___x_27_ = v___x_18_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v_head_15_);
lean_ctor_set(v_reuseFailAlloc_32_, 1, v_snd_21_);
v___x_27_ = v_reuseFailAlloc_32_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
lean_object* v___x_29_; 
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 1, v___x_27_);
v___x_29_ = v___x_23_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_fst_20_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v___x_27_);
v___x_29_ = v_reuseFailAlloc_31_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
v_a_2_ = v_tail_16_;
v_a_3_ = v___x_29_;
goto _start;
}
}
}
v___jp_33_:
{
if (v___y_34_ == 0)
{
goto v___jp_25_;
}
else
{
lean_object* v___x_35_; lean_object* v___x_36_; 
lean_del_object(v___x_23_);
lean_del_object(v___x_18_);
v___x_35_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_35_, 0, v_head_15_);
lean_ctor_set(v___x_35_, 1, v_fst_20_);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v_snd_21_);
v_a_2_ = v_tail_16_;
v_a_3_ = v___x_36_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_List_mapTR_loop___at___00main_spec__3___closed__4(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_53_ = ((lean_object*)(l_List_mapTR_loop___at___00main_spec__3___closed__3));
v___x_54_ = lean_unsigned_to_nat(14u);
v___x_55_ = lean_unsigned_to_nat(22u);
v___x_56_ = ((lean_object*)(l_List_mapTR_loop___at___00main_spec__3___closed__2));
v___x_57_ = ((lean_object*)(l_List_mapTR_loop___at___00main_spec__3___closed__1));
v___x_58_ = l_mkPanicMessageWithDecl(v___x_57_, v___x_56_, v___x_55_, v___x_54_, v___x_53_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00main_spec__3(lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
if (lean_obj_tag(v_a_59_) == 0)
{
lean_object* v___x_61_; 
v___x_61_ = l_List_reverse___redArg(v_a_60_);
return v___x_61_;
}
else
{
lean_object* v_head_62_; lean_object* v_tail_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_79_; 
v_head_62_ = lean_ctor_get(v_a_59_, 0);
v_tail_63_ = lean_ctor_get(v_a_59_, 1);
v_isSharedCheck_79_ = !lean_is_exclusive(v_a_59_);
if (v_isSharedCheck_79_ == 0)
{
v___x_65_ = v_a_59_;
v_isShared_66_ = v_isSharedCheck_79_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_tail_63_);
lean_inc(v_head_62_);
lean_dec(v_a_59_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_79_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___y_68_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = ((lean_object*)(l_List_mapTR_loop___at___00main_spec__3___closed__0));
v___x_74_ = lean_string_append(v___x_73_, v_head_62_);
lean_dec(v_head_62_);
v___x_75_ = l_Lean_Syntax_decodeNameLit(v___x_74_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_obj_once(&l_List_mapTR_loop___at___00main_spec__3___closed__4, &l_List_mapTR_loop___at___00main_spec__3___closed__4_once, _init_l_List_mapTR_loop___at___00main_spec__3___closed__4);
v___x_77_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore_spec__0(v___x_76_);
v___y_68_ = v___x_77_;
goto v___jp_67_;
}
else
{
lean_object* v_val_78_; 
v_val_78_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_val_78_);
lean_dec_ref_known(v___x_75_, 1);
v___y_68_ = v_val_78_;
goto v___jp_67_;
}
v___jp_67_:
{
lean_object* v___x_70_; 
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v_a_60_);
lean_ctor_set(v___x_65_, 0, v___y_68_);
v___x_70_ = v___x_65_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___y_68_);
lean_ctor_set(v_reuseFailAlloc_72_, 1, v_a_60_);
v___x_70_ = v_reuseFailAlloc_72_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
v_a_59_ = v_tail_63_;
v_a_60_ = v___x_70_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_span_loop___at___00main_spec__1(lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
if (lean_obj_tag(v_a_80_) == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = l_List_reverse___redArg(v_a_81_);
v___x_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v_a_80_);
return v___x_83_;
}
else
{
lean_object* v_head_84_; lean_object* v_tail_85_; lean_object* v___x_86_; uint8_t v___x_87_; 
v_head_84_ = lean_ctor_get(v_a_80_, 0);
v_tail_85_ = lean_ctor_get(v_a_80_, 1);
v___x_86_ = ((lean_object*)(l_List_partition_loop___at___00main_spec__0___closed__0));
v___x_87_ = lean_string_dec_eq(v_head_84_, v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_95_; 
lean_inc(v_tail_85_);
lean_inc(v_head_84_);
v_isSharedCheck_95_ = !lean_is_exclusive(v_a_80_);
if (v_isSharedCheck_95_ == 0)
{
lean_object* v_unused_96_; lean_object* v_unused_97_; 
v_unused_96_ = lean_ctor_get(v_a_80_, 1);
lean_dec(v_unused_96_);
v_unused_97_ = lean_ctor_get(v_a_80_, 0);
lean_dec(v_unused_97_);
v___x_89_ = v_a_80_;
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
else
{
lean_dec(v_a_80_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v_a_81_);
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_head_84_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v_a_81_);
v___x_92_ = v_reuseFailAlloc_94_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
v_a_80_ = v_tail_85_;
v_a_81_ = v___x_92_;
goto _start;
}
}
}
else
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = l_List_reverse___redArg(v_a_81_);
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v_a_80_);
return v___x_99_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2(size_t v_sz_100_, size_t v_i_101_, lean_object* v_bs_102_){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = lean_usize_dec_lt(v_i_101_, v_sz_100_);
if (v___x_103_ == 0)
{
return v_bs_102_;
}
else
{
lean_object* v_v_104_; lean_object* v___x_105_; lean_object* v_bs_x27_106_; lean_object* v___y_108_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_v_104_ = lean_array_uget(v_bs_102_, v_i_101_);
v___x_105_ = lean_unsigned_to_nat(0u);
v_bs_x27_106_ = lean_array_uset(v_bs_102_, v_i_101_, v___x_105_);
v___x_115_ = ((lean_object*)(l_List_mapTR_loop___at___00main_spec__3___closed__0));
v___x_116_ = lean_string_append(v___x_115_, v_v_104_);
lean_dec(v_v_104_);
v___x_117_ = l_Lean_Syntax_decodeNameLit(v___x_116_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_obj_once(&l_List_mapTR_loop___at___00main_spec__3___closed__4, &l_List_mapTR_loop___at___00main_spec__3___closed__4_once, _init_l_List_mapTR_loop___at___00main_spec__3___closed__4);
v___x_119_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore_spec__0(v___x_118_);
v___y_108_ = v___x_119_;
goto v___jp_107_;
}
else
{
lean_object* v_val_120_; 
v_val_120_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_val_120_);
lean_dec_ref_known(v___x_117_, 1);
v___y_108_ = v_val_120_;
goto v___jp_107_;
}
v___jp_107_:
{
uint8_t v___x_109_; lean_object* v___x_110_; size_t v___x_111_; size_t v___x_112_; lean_object* v___x_113_; 
v___x_109_ = 0;
v___x_110_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_110_, 0, v___y_108_);
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*1, v___x_109_);
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*1 + 1, v___x_103_);
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*1 + 2, v___x_109_);
v___x_111_ = ((size_t)1ULL);
v___x_112_ = lean_usize_add(v_i_101_, v___x_111_);
v___x_113_ = lean_array_uset(v_bs_x27_106_, v_i_101_, v___x_110_);
v_i_101_ = v___x_112_;
v_bs_102_ = v___x_113_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_100_ = stack[0].m_num;
size_t v_i_101_ = stack[1].m_num;
lean_object* v_bs_102_ = stack[2].m_obj;
lean_object* v_res_121_;
v_res_121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2(v_sz_100_, v_i_101_, v_bs_102_);
stack->m_obj
 = v_res_121_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___boxed(lean_object* v_sz_122_, lean_object* v_i_123_, lean_object* v_bs_124_){
_start:
{
size_t v_sz_boxed_125_; size_t v_i_boxed_126_; lean_object* v_res_127_; 
v_sz_boxed_125_ = lean_unbox_usize(v_sz_122_);
lean_dec(v_sz_122_);
v_i_boxed_126_ = lean_unbox_usize(v_i_123_);
lean_dec(v_i_123_);
v_res_127_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2(v_sz_boxed_125_, v_i_boxed_126_, v_bs_124_);
return v_res_127_;
}
}
lean_object* _lean_main(lean_object* v_args_133_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = ((lean_object*)(l_main___closed__0));
v___x_136_ = l_Lean_findSysroot(v___x_135_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v_a_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_a_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_a_137_);
lean_dec_ref_known(v___x_136_, 1);
v___x_138_ = lean_box(0);
v___x_139_ = l_Lean_initSearchPath(v_a_137_, v___x_138_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v_fst_142_; lean_object* v_snd_143_; lean_object* v___x_144_; lean_object* v_fst_145_; lean_object* v_snd_146_; lean_object* v___x_147_; size_t v_sz_148_; size_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; uint32_t v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; uint8_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec_ref_known(v___x_139_, 1);
v___x_140_ = ((lean_object*)(l_main___closed__1));
v___x_141_ = l_List_partition_loop___at___00main_spec__0(v_args_133_, v___x_140_);
v_fst_142_ = lean_ctor_get(v___x_141_, 0);
lean_inc(v_fst_142_);
v_snd_143_ = lean_ctor_get(v___x_141_, 1);
lean_inc(v_snd_143_);
lean_dec_ref(v___x_141_);
v___x_144_ = l_List_span_loop___at___00main_spec__1(v_snd_143_, v___x_138_);
v_fst_145_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_fst_145_);
v_snd_146_ = lean_ctor_get(v___x_144_, 1);
lean_inc(v_snd_146_);
lean_dec_ref(v___x_144_);
v___x_147_ = lean_array_mk(v_fst_145_);
v_sz_148_ = lean_array_size(v___x_147_);
v___x_149_ = ((size_t)0ULL);
v___x_150_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2(v_sz_148_, v___x_149_, v___x_147_);
v___x_151_ = l_Lean_Options_empty;
v___x_152_ = 0;
v___x_153_ = ((lean_object*)(l_main___closed__2));
v___x_154_ = 0;
v___x_155_ = 2;
v___x_156_ = lean_box(1);
v___x_157_ = l_Lean_importModules(v___x_150_, v___x_151_, v___x_152_, v___x_153_, v___x_154_, v___x_154_, v___x_155_, v___x_156_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; lean_object* v___x_159_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_a_158_);
lean_dec_ref_known(v___x_157_, 1);
v___x_159_ = l_List_tail_x3f___redArg(v_snd_146_);
lean_dec(v_snd_146_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_box(0);
v___x_161_ = l_LeanExport_dumpEnv(v_a_158_, v___x_160_, v_fst_142_);
return v___x_161_;
}
else
{
lean_object* v_val_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_171_; 
v_val_162_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_171_ == 0)
{
v___x_164_ = v___x_159_;
v_isShared_165_ = v_isSharedCheck_171_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_val_162_);
lean_dec(v___x_159_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_171_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_166_ = l_List_mapTR_loop___at___00main_spec__3(v_val_162_, v___x_138_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_166_);
v___x_168_ = v___x_164_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_166_);
v___x_168_ = v_reuseFailAlloc_170_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_169_; 
v___x_169_ = l_LeanExport_dumpEnv(v_a_158_, v___x_168_, v_fst_142_);
return v___x_169_;
}
}
}
}
else
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
lean_dec(v_snd_146_);
lean_dec(v_fst_142_);
v_a_172_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_179_ == 0)
{
v___x_174_ = v___x_157_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_157_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_172_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
else
{
lean_dec(v_args_133_);
return v___x_139_;
}
}
else
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_187_; 
lean_dec(v_args_133_);
v_a_180_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_187_ == 0)
{
v___x_182_ = v___x_136_;
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_136_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_185_; 
if (v_isShared_183_ == 0)
{
v___x_185_ = v___x_182_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_a_180_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
}
LEAN_EXPORT void _lean_main_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_133_ = stack[0].m_obj;
lean_object* v_res_188_;
v_res_188_ = _lean_main(v_args_133_);
stack->m_obj
 = v_res_188_;
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = _lean_main(v_args_189_);
return v_res_191_;
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
