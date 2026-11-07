// Lean compiler output
// Module: Lean.Data.Markdown.Parser.Children
// Imports: import Init public import Lean.Data.Markdown.Block
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Markdown_ListKind_sameKind(lean_object*, lean_object*);
static const lean_array_object l_Lean_Markdown_Children_empty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Markdown_Children_empty___redArg___closed__0 = (const lean_object*)&l_Lean_Markdown_Children_empty___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Markdown_Children_empty___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Markdown_Children_empty___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Markdown_Children_empty___redArg___closed__1 = (const lean_object*)&l_Lean_Markdown_Children_empty___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_empty___redArg();
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Markdown_Children_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_Children_empty___closed__0;
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_empty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_instEmptyCollection___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_instEmptyCollection___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_instInhabited___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_instInhabited___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_Children_flushLists_spec__0___redArg(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_Children_flushLists_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_flushLists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_flushLists___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_Children_flushLists_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_Children_flushLists_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_push(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_push___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_setPendingList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_setPendingList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_takePendingList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_takePendingList___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_takePendingList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_takePendingList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Markdown_Children_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Markdown_Children_isEmpty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_isEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_empty___redArg(){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = ((lean_object*)(l_Lean_Markdown_Children_empty___redArg___closed__1));
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_empty___redArg___boxed(lean_object* v___dummy_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Markdown_Children_empty___redArg();
return v_res_9_;
}
}
static lean_object* _init_l_Lean_Markdown_Children_empty___closed__0(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Markdown_Children_empty___redArg();
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_empty(lean_object* v_s_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Lean_Markdown_Children_empty___closed__0, &l_Lean_Markdown_Children_empty___closed__0_once, _init_l_Lean_Markdown_Children_empty___closed__0);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_empty___boxed(lean_object* v_s_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_Markdown_Children_empty(v_s_13_);
lean_dec_ref(v_s_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_obj_once(&l_Lean_Markdown_Children_empty___closed__0, &l_Lean_Markdown_Children_empty___closed__0_once, _init_l_Lean_Markdown_Children_empty___closed__0);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_instEmptyCollection___redArg___boxed(lean_object* v___dummy_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Markdown_Children_instEmptyCollection___redArg();
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_instEmptyCollection(lean_object* v_s_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_obj_once(&l_Lean_Markdown_Children_empty___closed__0, &l_Lean_Markdown_Children_empty___closed__0_once, _init_l_Lean_Markdown_Children_empty___closed__0);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_instEmptyCollection___boxed(lean_object* v_s_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Markdown_Children_instEmptyCollection(v_s_21_);
lean_dec_ref(v_s_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_instInhabited___redArg(){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_obj_once(&l_Lean_Markdown_Children_empty___closed__0, &l_Lean_Markdown_Children_empty___closed__0_once, _init_l_Lean_Markdown_Children_empty___closed__0);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_instInhabited___redArg___boxed(lean_object* v___dummy_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Markdown_Children_instInhabited___redArg();
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_instInhabited(lean_object* v_s_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_obj_once(&l_Lean_Markdown_Children_empty___closed__0, &l_Lean_Markdown_Children_empty___closed__0_once, _init_l_Lean_Markdown_Children_empty___closed__0);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_instInhabited___boxed(lean_object* v_s_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Markdown_Children_instInhabited(v_s_29_);
lean_dec_ref(v_s_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_Children_flushLists_spec__0___redArg(size_t v_sz_31_, size_t v_i_32_, lean_object* v_bs_33_){
_start:
{
uint8_t v___x_34_; 
v___x_34_ = lean_usize_dec_lt(v_i_32_, v_sz_31_);
if (v___x_34_ == 0)
{
return v_bs_33_;
}
else
{
lean_object* v_v_35_; lean_object* v_marker_36_; lean_object* v_children_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_50_; 
v_v_35_ = lean_array_uget(v_bs_33_, v_i_32_);
v_marker_36_ = lean_ctor_get(v_v_35_, 0);
v_children_37_ = lean_ctor_get(v_v_35_, 1);
v_isSharedCheck_50_ = !lean_is_exclusive(v_v_35_);
if (v_isSharedCheck_50_ == 0)
{
v___x_39_ = v_v_35_;
v_isShared_40_ = v_isSharedCheck_50_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_children_37_);
lean_inc(v_marker_36_);
lean_dec(v_v_35_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_50_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_41_; lean_object* v_bs_x27_42_; lean_object* v___x_44_; 
v___x_41_ = lean_unsigned_to_nat(0u);
v_bs_x27_42_ = lean_array_uset(v_bs_33_, v_i_32_, v___x_41_);
if (v_isShared_40_ == 0)
{
lean_ctor_set_tag(v___x_39_, 8);
v___x_44_ = v___x_39_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_marker_36_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v_children_37_);
v___x_44_ = v_reuseFailAlloc_49_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
size_t v___x_45_; size_t v___x_46_; lean_object* v___x_47_; 
v___x_45_ = ((size_t)1ULL);
v___x_46_ = lean_usize_add(v_i_32_, v___x_45_);
v___x_47_ = lean_array_uset(v_bs_x27_42_, v_i_32_, v___x_44_);
v_i_32_ = v___x_46_;
v_bs_33_ = v___x_47_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_Children_flushLists_spec__0___redArg___boxed(lean_object* v_sz_51_, lean_object* v_i_52_, lean_object* v_bs_53_){
_start:
{
size_t v_sz_boxed_54_; size_t v_i_boxed_55_; lean_object* v_res_56_; 
v_sz_boxed_54_ = lean_unbox_usize(v_sz_51_);
lean_dec(v_sz_51_);
v_i_boxed_55_ = lean_unbox_usize(v_i_52_);
lean_dec(v_i_52_);
v_res_56_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_Children_flushLists_spec__0___redArg(v_sz_boxed_54_, v_i_boxed_55_, v_bs_53_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_flushLists(lean_object* v_s_57_, lean_object* v_c_58_){
_start:
{
lean_object* v_pendingList_x3f_59_; 
v_pendingList_x3f_59_ = lean_ctor_get(v_c_58_, 1);
if (lean_obj_tag(v_pendingList_x3f_59_) == 1)
{
lean_object* v_val_60_; lean_object* v_blocks_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_87_; 
v_val_60_ = lean_ctor_get(v_pendingList_x3f_59_, 0);
lean_inc(v_val_60_);
v_blocks_61_ = lean_ctor_get(v_c_58_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v_c_58_);
if (v_isSharedCheck_87_ == 0)
{
lean_object* v_unused_88_; 
v_unused_88_ = lean_ctor_get(v_c_58_, 1);
lean_dec(v_unused_88_);
v___x_63_ = v_c_58_;
v_isShared_64_ = v_isSharedCheck_87_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_blocks_61_);
lean_dec(v_c_58_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_87_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v_kind_65_; uint8_t v_loose_66_; lean_object* v_items_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_86_; 
v_kind_65_ = lean_ctor_get(v_val_60_, 0);
v_loose_66_ = lean_ctor_get_uint8(v_val_60_, sizeof(void*)*2);
v_items_67_ = lean_ctor_get(v_val_60_, 1);
v_isSharedCheck_86_ = !lean_is_exclusive(v_val_60_);
if (v_isSharedCheck_86_ == 0)
{
v___x_69_ = v_val_60_;
v_isShared_70_ = v_isSharedCheck_86_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_items_67_);
lean_inc(v_kind_65_);
lean_dec(v_val_60_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_86_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
size_t v_sz_71_; size_t v___x_72_; lean_object* v_items_73_; uint8_t v___y_75_; 
v_sz_71_ = lean_array_size(v_items_67_);
v___x_72_ = ((size_t)0ULL);
v_items_73_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_Children_flushLists_spec__0___redArg(v_sz_71_, v___x_72_, v_items_67_);
if (v_loose_66_ == 0)
{
uint8_t v___x_84_; 
v___x_84_ = 1;
v___y_75_ = v___x_84_;
goto v___jp_74_;
}
else
{
uint8_t v___x_85_; 
v___x_85_ = 0;
v___y_75_ = v___x_85_;
goto v___jp_74_;
}
v___jp_74_:
{
lean_object* v___x_77_; 
if (v_isShared_70_ == 0)
{
lean_ctor_set_tag(v___x_69_, 7);
lean_ctor_set(v___x_69_, 1, v_items_73_);
v___x_77_ = v___x_69_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(7, 2, 1);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_kind_65_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v_items_73_);
v___x_77_ = v_reuseFailAlloc_83_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_81_; 
lean_ctor_set_uint8(v___x_77_, sizeof(void*)*2, v___y_75_);
v___x_78_ = lean_array_push(v_blocks_61_, v___x_77_);
v___x_79_ = lean_box(0);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 1, v___x_79_);
lean_ctor_set(v___x_63_, 0, v___x_78_);
v___x_81_ = v___x_63_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_78_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v___x_79_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
}
}
else
{
lean_object* v_blocks_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
lean_inc(v_pendingList_x3f_59_);
v_blocks_89_ = lean_ctor_get(v_c_58_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v_c_58_);
if (v_isSharedCheck_96_ == 0)
{
lean_object* v_unused_97_; 
v_unused_97_ = lean_ctor_get(v_c_58_, 1);
lean_dec(v_unused_97_);
v___x_91_ = v_c_58_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_blocks_89_);
lean_dec(v_c_58_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_blocks_89_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v_pendingList_x3f_59_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_flushLists___boxed(lean_object* v_s_98_, lean_object* v_c_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Markdown_Children_flushLists(v_s_98_, v_c_99_);
lean_dec_ref(v_s_98_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_Children_flushLists_spec__0(lean_object* v_s_101_, size_t v_sz_102_, size_t v_i_103_, lean_object* v_bs_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_Children_flushLists_spec__0___redArg(v_sz_102_, v_i_103_, v_bs_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_Children_flushLists_spec__0___boxed(lean_object* v_s_106_, lean_object* v_sz_107_, lean_object* v_i_108_, lean_object* v_bs_109_){
_start:
{
size_t v_sz_boxed_110_; size_t v_i_boxed_111_; lean_object* v_res_112_; 
v_sz_boxed_110_ = lean_unbox_usize(v_sz_107_);
lean_dec(v_sz_107_);
v_i_boxed_111_ = lean_unbox_usize(v_i_108_);
lean_dec(v_i_108_);
v_res_112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_Children_flushLists_spec__0(v_s_106_, v_sz_boxed_110_, v_i_boxed_111_, v_bs_109_);
lean_dec_ref(v_s_106_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_push(lean_object* v_s_113_, lean_object* v_c_114_, lean_object* v_b_115_){
_start:
{
lean_object* v_c_116_; lean_object* v_blocks_117_; lean_object* v_pendingList_x3f_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_126_; 
v_c_116_ = l_Lean_Markdown_Children_flushLists(v_s_113_, v_c_114_);
v_blocks_117_ = lean_ctor_get(v_c_116_, 0);
v_pendingList_x3f_118_ = lean_ctor_get(v_c_116_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v_c_116_);
if (v_isSharedCheck_126_ == 0)
{
v___x_120_ = v_c_116_;
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_pendingList_x3f_118_);
lean_inc(v_blocks_117_);
lean_dec(v_c_116_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_122_ = lean_array_push(v_blocks_117_, v_b_115_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_122_);
v___x_124_ = v___x_120_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_pendingList_x3f_118_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_push___boxed(lean_object* v_s_127_, lean_object* v_c_128_, lean_object* v_b_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Markdown_Children_push(v_s_127_, v_c_128_, v_b_129_);
lean_dec_ref(v_s_127_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_setPendingList(lean_object* v_s_131_, lean_object* v_c_132_, lean_object* v_list_133_){
_start:
{
lean_object* v___x_134_; lean_object* v_blocks_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_143_; 
v___x_134_ = l_Lean_Markdown_Children_flushLists(v_s_131_, v_c_132_);
v_blocks_135_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_143_ == 0)
{
lean_object* v_unused_144_; 
v_unused_144_ = lean_ctor_get(v___x_134_, 1);
lean_dec(v_unused_144_);
v___x_137_ = v___x_134_;
v_isShared_138_ = v_isSharedCheck_143_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_blocks_135_);
lean_dec(v___x_134_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_143_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_139_, 0, v_list_133_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 1, v___x_139_);
v___x_141_ = v___x_137_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_blocks_135_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_setPendingList___boxed(lean_object* v_s_145_, lean_object* v_c_146_, lean_object* v_list_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Markdown_Children_setPendingList(v_s_145_, v_c_146_, v_list_147_);
lean_dec_ref(v_s_145_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_takePendingList___redArg(lean_object* v_c_149_, lean_object* v_kind_150_){
_start:
{
lean_object* v_pendingList_x3f_151_; 
v_pendingList_x3f_151_ = lean_ctor_get(v_c_149_, 1);
lean_inc(v_pendingList_x3f_151_);
if (lean_obj_tag(v_pendingList_x3f_151_) == 1)
{
lean_object* v_val_152_; lean_object* v_blocks_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_169_; 
v_val_152_ = lean_ctor_get(v_pendingList_x3f_151_, 0);
v_blocks_153_ = lean_ctor_get(v_c_149_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v_c_149_);
if (v_isSharedCheck_169_ == 0)
{
lean_object* v_unused_170_; 
v_unused_170_ = lean_ctor_get(v_c_149_, 1);
lean_dec(v_unused_170_);
v___x_155_ = v_c_149_;
v_isShared_156_ = v_isSharedCheck_169_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_blocks_153_);
lean_dec(v_c_149_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_169_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v_kind_157_; uint8_t v___x_158_; 
v_kind_157_ = lean_ctor_get(v_val_152_, 0);
v___x_158_ = l_Lean_Markdown_ListKind_sameKind(v_kind_157_, v_kind_150_);
if (v___x_158_ == 0)
{
lean_object* v___x_160_; 
if (v_isShared_156_ == 0)
{
v___x_160_ = v___x_155_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_blocks_153_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_pendingList_x3f_151_);
v___x_160_ = v_reuseFailAlloc_163_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_box(0);
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_160_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
return v___x_162_;
}
}
else
{
lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_164_ = lean_box(0);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 1, v___x_164_);
v___x_166_ = v___x_155_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_blocks_153_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v___x_164_);
v___x_166_ = v_reuseFailAlloc_168_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; 
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v_pendingList_x3f_151_);
return v___x_167_;
}
}
}
}
else
{
lean_object* v_blocks_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_180_; 
v_blocks_171_ = lean_ctor_get(v_c_149_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v_c_149_);
if (v_isSharedCheck_180_ == 0)
{
lean_object* v_unused_181_; 
v_unused_181_ = lean_ctor_get(v_c_149_, 1);
lean_dec(v_unused_181_);
v___x_173_ = v_c_149_;
v_isShared_174_ = v_isSharedCheck_180_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_blocks_171_);
lean_dec(v_c_149_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_180_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_blocks_171_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_pendingList_x3f_151_);
v___x_176_ = v_reuseFailAlloc_179_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_box(0);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_176_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
return v___x_178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_takePendingList___redArg___boxed(lean_object* v_c_182_, lean_object* v_kind_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Markdown_Children_takePendingList___redArg(v_c_182_, v_kind_183_);
lean_dec_ref(v_kind_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_takePendingList(lean_object* v_s_185_, lean_object* v_c_186_, lean_object* v_kind_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_Markdown_Children_takePendingList___redArg(v_c_186_, v_kind_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_takePendingList___boxed(lean_object* v_s_189_, lean_object* v_c_190_, lean_object* v_kind_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Markdown_Children_takePendingList(v_s_189_, v_c_190_, v_kind_191_);
lean_dec_ref(v_kind_191_);
lean_dec_ref(v_s_189_);
return v_res_192_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_Children_isEmpty___redArg(lean_object* v_c_193_){
_start:
{
lean_object* v_blocks_194_; lean_object* v_pendingList_x3f_195_; lean_object* v___x_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v_blocks_194_ = lean_ctor_get(v_c_193_, 0);
v_pendingList_x3f_195_ = lean_ctor_get(v_c_193_, 1);
v___x_196_ = lean_array_get_size(v_blocks_194_);
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = lean_nat_dec_eq(v___x_196_, v___x_197_);
if (v___x_198_ == 0)
{
return v___x_198_;
}
else
{
if (lean_obj_tag(v_pendingList_x3f_195_) == 0)
{
return v___x_198_;
}
else
{
uint8_t v___x_199_; 
v___x_199_ = 0;
return v___x_199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_isEmpty___redArg___boxed(lean_object* v_c_200_){
_start:
{
uint8_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l_Lean_Markdown_Children_isEmpty___redArg(v_c_200_);
lean_dec_ref(v_c_200_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT uint8_t l_Lean_Markdown_Children_isEmpty(lean_object* v_s_203_, lean_object* v_c_204_){
_start:
{
uint8_t v___x_205_; 
v___x_205_ = l_Lean_Markdown_Children_isEmpty___redArg(v_c_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_Children_isEmpty___boxed(lean_object* v_s_206_, lean_object* v_c_207_){
_start:
{
uint8_t v_res_208_; lean_object* v_r_209_; 
v_res_208_ = l_Lean_Markdown_Children_isEmpty(v_s_206_, v_c_207_);
lean_dec_ref(v_c_207_);
lean_dec_ref(v_s_206_);
v_r_209_ = lean_box(v_res_208_);
return v_r_209_;
}
}
lean_object* runtime_initialize_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Block(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Markdown_Parser_Children(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Block(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Markdown_Parser_Children(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Block(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Markdown_Parser_Children(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Block(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Parser_Children(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Markdown_Parser_Children(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Markdown_Parser_Children(builtin);
}
#ifdef __cplusplus
}
#endif
