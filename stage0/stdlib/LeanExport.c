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
static lean_once_cell_t l_List_partition_loop___at___00main_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_partition_loop___at___00main_spec__0___closed__1;
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
static lean_object* _init_l_List_partition_loop___at___00main_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = ((lean_object*)(l_List_partition_loop___at___00main_spec__0___closed__0));
v___x_3_ = lean_string_utf8_byte_size(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_List_partition_loop___at___00main_spec__0(lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
if (lean_obj_tag(v_a_4_) == 0)
{
lean_object* v_fst_6_; lean_object* v_snd_7_; lean_object* v___x_9_; uint8_t v_isShared_10_; uint8_t v_isSharedCheck_16_; 
v_fst_6_ = lean_ctor_get(v_a_5_, 0);
v_snd_7_ = lean_ctor_get(v_a_5_, 1);
v_isSharedCheck_16_ = !lean_is_exclusive(v_a_5_);
if (v_isSharedCheck_16_ == 0)
{
v___x_9_ = v_a_5_;
v_isShared_10_ = v_isSharedCheck_16_;
goto v_resetjp_8_;
}
else
{
lean_inc(v_snd_7_);
lean_inc(v_fst_6_);
lean_dec(v_a_5_);
v___x_9_ = lean_box(0);
v_isShared_10_ = v_isSharedCheck_16_;
goto v_resetjp_8_;
}
v_resetjp_8_:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_14_; 
v___x_11_ = l_List_reverse___redArg(v_fst_6_);
v___x_12_ = l_List_reverse___redArg(v_snd_7_);
if (v_isShared_10_ == 0)
{
lean_ctor_set(v___x_9_, 1, v___x_12_);
lean_ctor_set(v___x_9_, 0, v___x_11_);
v___x_14_ = v___x_9_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v___x_11_);
lean_ctor_set(v_reuseFailAlloc_15_, 1, v___x_12_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
else
{
lean_object* v_head_17_; lean_object* v_tail_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_50_; 
v_head_17_ = lean_ctor_get(v_a_4_, 0);
v_tail_18_ = lean_ctor_get(v_a_4_, 1);
v_isSharedCheck_50_ = !lean_is_exclusive(v_a_4_);
if (v_isSharedCheck_50_ == 0)
{
v___x_20_ = v_a_4_;
v_isShared_21_ = v_isSharedCheck_50_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_tail_18_);
lean_inc(v_head_17_);
lean_dec(v_a_4_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_50_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v_fst_22_; lean_object* v_snd_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_49_; 
v_fst_22_ = lean_ctor_get(v_a_5_, 0);
v_snd_23_ = lean_ctor_get(v_a_5_, 1);
v_isSharedCheck_49_ = !lean_is_exclusive(v_a_5_);
if (v_isSharedCheck_49_ == 0)
{
v___x_25_ = v_a_5_;
v_isShared_26_ = v_isSharedCheck_49_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_snd_23_);
lean_inc(v_fst_22_);
lean_dec(v_a_5_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_49_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
uint8_t v___y_36_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v___x_40_ = ((lean_object*)(l_List_partition_loop___at___00main_spec__0___closed__0));
v___x_41_ = lean_string_utf8_byte_size(v_head_17_);
v___x_42_ = lean_obj_once(&l_List_partition_loop___at___00main_spec__0___closed__1, &l_List_partition_loop___at___00main_spec__0___closed__1_once, _init_l_List_partition_loop___at___00main_spec__0___closed__1);
v___x_43_ = lean_nat_dec_le(v___x_42_, v___x_41_);
if (v___x_43_ == 0)
{
goto v___jp_27_;
}
else
{
lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = lean_string_memcmp(v_head_17_, v___x_40_, v___x_44_, v___x_44_, v___x_42_);
if (v___x_45_ == 0)
{
v___y_36_ = v___x_45_;
goto v___jp_35_;
}
else
{
lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_46_ = lean_unsigned_to_nat(3u);
v___x_47_ = lean_string_length(v_head_17_);
v___x_48_ = lean_nat_dec_le(v___x_46_, v___x_47_);
v___y_36_ = v___x_48_;
goto v___jp_35_;
}
}
v___jp_27_:
{
lean_object* v___x_29_; 
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 1, v_snd_23_);
v___x_29_ = v___x_20_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_head_17_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v_snd_23_);
v___x_29_ = v_reuseFailAlloc_34_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
lean_object* v___x_31_; 
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 1, v___x_29_);
v___x_31_ = v___x_25_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v_fst_22_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v___x_29_);
v___x_31_ = v_reuseFailAlloc_33_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
v_a_4_ = v_tail_18_;
v_a_5_ = v___x_31_;
goto _start;
}
}
}
v___jp_35_:
{
if (v___y_36_ == 0)
{
goto v___jp_27_;
}
else
{
lean_object* v___x_37_; lean_object* v___x_38_; 
lean_del_object(v___x_25_);
lean_del_object(v___x_20_);
v___x_37_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_37_, 0, v_head_17_);
lean_ctor_set(v___x_37_, 1, v_fst_22_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v_snd_23_);
v_a_4_ = v_tail_18_;
v_a_5_ = v___x_38_;
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
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_55_ = ((lean_object*)(l_List_mapTR_loop___at___00main_spec__3___closed__3));
v___x_56_ = lean_unsigned_to_nat(14u);
v___x_57_ = lean_unsigned_to_nat(22u);
v___x_58_ = ((lean_object*)(l_List_mapTR_loop___at___00main_spec__3___closed__2));
v___x_59_ = ((lean_object*)(l_List_mapTR_loop___at___00main_spec__3___closed__1));
v___x_60_ = l_mkPanicMessageWithDecl(v___x_59_, v___x_58_, v___x_57_, v___x_56_, v___x_55_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00main_spec__3(lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
if (lean_obj_tag(v_a_61_) == 0)
{
lean_object* v___x_63_; 
v___x_63_ = l_List_reverse___redArg(v_a_62_);
return v___x_63_;
}
else
{
lean_object* v_head_64_; lean_object* v_tail_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_81_; 
v_head_64_ = lean_ctor_get(v_a_61_, 0);
v_tail_65_ = lean_ctor_get(v_a_61_, 1);
v_isSharedCheck_81_ = !lean_is_exclusive(v_a_61_);
if (v_isSharedCheck_81_ == 0)
{
v___x_67_ = v_a_61_;
v_isShared_68_ = v_isSharedCheck_81_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_tail_65_);
lean_inc(v_head_64_);
lean_dec(v_a_61_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_81_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___y_70_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_75_ = ((lean_object*)(l_List_mapTR_loop___at___00main_spec__3___closed__0));
v___x_76_ = lean_string_append(v___x_75_, v_head_64_);
lean_dec(v_head_64_);
v___x_77_ = l_Lean_Syntax_decodeNameLit(v___x_76_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_obj_once(&l_List_mapTR_loop___at___00main_spec__3___closed__4, &l_List_mapTR_loop___at___00main_spec__3___closed__4_once, _init_l_List_mapTR_loop___at___00main_spec__3___closed__4);
v___x_79_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore_spec__0(v___x_78_);
v___y_70_ = v___x_79_;
goto v___jp_69_;
}
else
{
lean_object* v_val_80_; 
v_val_80_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v_val_80_);
lean_dec_ref_known(v___x_77_, 1);
v___y_70_ = v_val_80_;
goto v___jp_69_;
}
v___jp_69_:
{
lean_object* v___x_72_; 
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 1, v_a_62_);
lean_ctor_set(v___x_67_, 0, v___y_70_);
v___x_72_ = v___x_67_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___y_70_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_a_62_);
v___x_72_ = v_reuseFailAlloc_74_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
v_a_61_ = v_tail_65_;
v_a_62_ = v___x_72_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_span_loop___at___00main_spec__1(lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
if (lean_obj_tag(v_a_82_) == 0)
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = l_List_reverse___redArg(v_a_83_);
v___x_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v_a_82_);
return v___x_85_;
}
else
{
lean_object* v_head_86_; lean_object* v_tail_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v_head_86_ = lean_ctor_get(v_a_82_, 0);
v_tail_87_ = lean_ctor_get(v_a_82_, 1);
v___x_88_ = ((lean_object*)(l_List_partition_loop___at___00main_spec__0___closed__0));
v___x_89_ = lean_string_dec_eq(v_head_86_, v___x_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_97_; 
lean_inc(v_tail_87_);
lean_inc(v_head_86_);
v_isSharedCheck_97_ = !lean_is_exclusive(v_a_82_);
if (v_isSharedCheck_97_ == 0)
{
lean_object* v_unused_98_; lean_object* v_unused_99_; 
v_unused_98_ = lean_ctor_get(v_a_82_, 1);
lean_dec(v_unused_98_);
v_unused_99_ = lean_ctor_get(v_a_82_, 0);
lean_dec(v_unused_99_);
v___x_91_ = v_a_82_;
v_isShared_92_ = v_isSharedCheck_97_;
goto v_resetjp_90_;
}
else
{
lean_dec(v_a_82_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_97_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 1, v_a_83_);
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_head_86_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_a_83_);
v___x_94_ = v_reuseFailAlloc_96_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
v_a_82_ = v_tail_87_;
v_a_83_ = v___x_94_;
goto _start;
}
}
}
else
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = l_List_reverse___redArg(v_a_83_);
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v_a_82_);
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2(size_t v_sz_102_, size_t v_i_103_, lean_object* v_bs_104_){
_start:
{
uint8_t v___x_105_; 
v___x_105_ = lean_usize_dec_lt(v_i_103_, v_sz_102_);
if (v___x_105_ == 0)
{
return v_bs_104_;
}
else
{
lean_object* v_v_106_; lean_object* v___x_107_; lean_object* v_bs_x27_108_; lean_object* v___y_110_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_v_106_ = lean_array_uget(v_bs_104_, v_i_103_);
v___x_107_ = lean_unsigned_to_nat(0u);
v_bs_x27_108_ = lean_array_uset(v_bs_104_, v_i_103_, v___x_107_);
v___x_117_ = ((lean_object*)(l_List_mapTR_loop___at___00main_spec__3___closed__0));
v___x_118_ = lean_string_append(v___x_117_, v_v_106_);
lean_dec(v_v_106_);
v___x_119_ = l_Lean_Syntax_decodeNameLit(v___x_118_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_obj_once(&l_List_mapTR_loop___at___00main_spec__3___closed__4, &l_List_mapTR_loop___at___00main_spec__3___closed__4_once, _init_l_List_mapTR_loop___at___00main_spec__3___closed__4);
v___x_121_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Order_Proof_0__Lean_Meta_Grind_Order_mkPropagateEqFalseProofCore_spec__0(v___x_120_);
v___y_110_ = v___x_121_;
goto v___jp_109_;
}
else
{
lean_object* v_val_122_; 
v_val_122_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_val_122_);
lean_dec_ref_known(v___x_119_, 1);
v___y_110_ = v_val_122_;
goto v___jp_109_;
}
v___jp_109_:
{
uint8_t v___x_111_; lean_object* v___x_112_; size_t v___x_113_; size_t v___x_114_; lean_object* v___x_115_; 
v___x_111_ = 0;
v___x_112_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_112_, 0, v___y_110_);
lean_ctor_set_uint8(v___x_112_, sizeof(void*)*1, v___x_111_);
lean_ctor_set_uint8(v___x_112_, sizeof(void*)*1 + 1, v___x_105_);
lean_ctor_set_uint8(v___x_112_, sizeof(void*)*1 + 2, v___x_111_);
v___x_113_ = ((size_t)1ULL);
v___x_114_ = lean_usize_add(v_i_103_, v___x_113_);
v___x_115_ = lean_array_uset(v_bs_x27_108_, v_i_103_, v___x_112_);
v_i_103_ = v___x_114_;
v_bs_104_ = v___x_115_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2___boxed(lean_object* v_sz_123_, lean_object* v_i_124_, lean_object* v_bs_125_){
_start:
{
size_t v_sz_boxed_126_; size_t v_i_boxed_127_; lean_object* v_res_128_; 
v_sz_boxed_126_ = lean_unbox_usize(v_sz_123_);
lean_dec(v_sz_123_);
v_i_boxed_127_ = lean_unbox_usize(v_i_124_);
lean_dec(v_i_124_);
v_res_128_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2(v_sz_boxed_126_, v_i_boxed_127_, v_bs_125_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_134_){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = ((lean_object*)(l_main___closed__0));
v___x_137_ = l_Lean_findSysroot(v___x_136_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_a_138_);
lean_dec_ref_known(v___x_137_, 1);
v___x_139_ = lean_box(0);
v___x_140_ = l_Lean_initSearchPath(v_a_138_, v___x_139_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v_fst_143_; lean_object* v_snd_144_; lean_object* v___x_145_; lean_object* v_fst_146_; lean_object* v_snd_147_; lean_object* v___x_148_; size_t v_sz_149_; size_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint32_t v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; uint8_t v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec_ref_known(v___x_140_, 1);
v___x_141_ = ((lean_object*)(l_main___closed__1));
v___x_142_ = l_List_partition_loop___at___00main_spec__0(v_args_134_, v___x_141_);
v_fst_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_fst_143_);
v_snd_144_ = lean_ctor_get(v___x_142_, 1);
lean_inc(v_snd_144_);
lean_dec_ref(v___x_142_);
v___x_145_ = l_List_span_loop___at___00main_spec__1(v_snd_144_, v___x_139_);
v_fst_146_ = lean_ctor_get(v___x_145_, 0);
lean_inc(v_fst_146_);
v_snd_147_ = lean_ctor_get(v___x_145_, 1);
lean_inc(v_snd_147_);
lean_dec_ref(v___x_145_);
v___x_148_ = lean_array_mk(v_fst_146_);
v_sz_149_ = lean_array_size(v___x_148_);
v___x_150_ = ((size_t)0ULL);
v___x_151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00main_spec__2(v_sz_149_, v___x_150_, v___x_148_);
v___x_152_ = l_Lean_Options_empty;
v___x_153_ = 0;
v___x_154_ = ((lean_object*)(l_main___closed__2));
v___x_155_ = 0;
v___x_156_ = 2;
v___x_157_ = lean_box(1);
v___x_158_ = l_Lean_importModules(v___x_151_, v___x_152_, v___x_153_, v___x_154_, v___x_155_, v___x_155_, v___x_156_, v___x_157_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_160_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v___x_158_, 1);
v___x_160_ = l_List_tail_x3f___redArg(v_snd_147_);
lean_dec(v_snd_147_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_box(0);
v___x_162_ = l_LeanExport_dumpEnv(v_a_159_, v___x_161_, v_fst_143_);
return v___x_162_;
}
else
{
lean_object* v_val_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_172_; 
v_val_163_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_172_ == 0)
{
v___x_165_ = v___x_160_;
v_isShared_166_ = v_isSharedCheck_172_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_val_163_);
lean_dec(v___x_160_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_172_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; lean_object* v___x_169_; 
v___x_167_ = l_List_mapTR_loop___at___00main_spec__3(v_val_163_, v___x_139_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_167_);
v___x_169_ = v___x_165_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_167_);
v___x_169_ = v_reuseFailAlloc_171_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
lean_object* v___x_170_; 
v___x_170_ = l_LeanExport_dumpEnv(v_a_159_, v___x_169_, v_fst_143_);
return v___x_170_;
}
}
}
}
else
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
lean_dec(v_snd_147_);
lean_dec(v_fst_143_);
v_a_173_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_158_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_158_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
else
{
lean_dec(v_args_134_);
return v___x_140_;
}
}
else
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
lean_dec(v_args_134_);
v_a_181_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_137_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_137_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
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
