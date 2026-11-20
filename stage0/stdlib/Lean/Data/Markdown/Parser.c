// Lean compiler output
// Module: Lean.Data.Markdown.Parser
// Imports: public import Lean.Data.Markdown.Parser.Block public import Lean.Data.Markdown.Parser.Inline
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Markdown_parseInlines(lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Markdown_parseBlocks(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_buildRefTable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseInlinesInBlock(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_parseInlinesInBlock_spec__0(lean_object*, lean_object*, uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_parseInlinesInBlock_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseInlinesInBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseDocument(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseDocument___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_parseInlinesInBlock(lean_object* v_s_1_, lean_object* v_refs_2_, lean_object* v_block_3_, uint8_t v_extensions_4_){
_start:
{
switch(lean_obj_tag(v_block_3_))
{
case 0:
{
lean_object* v_content_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_13_; 
v_content_5_ = lean_ctor_get(v_block_3_, 0);
v_isSharedCheck_13_ = !lean_is_exclusive(v_block_3_);
if (v_isSharedCheck_13_ == 0)
{
v___x_7_ = v_block_3_;
v_isShared_8_ = v_isSharedCheck_13_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_content_5_);
lean_dec(v_block_3_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_13_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; lean_object* v___x_11_; 
v___x_9_ = l_Lean_Markdown_parseInlines(v_s_1_, v_refs_2_, v_content_5_, v_extensions_4_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 0, v___x_9_);
v___x_11_ = v___x_7_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_12_; 
v_reuseFailAlloc_12_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_12_, 0, v___x_9_);
v___x_11_ = v_reuseFailAlloc_12_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
return v___x_11_;
}
}
}
case 1:
{
lean_object* v_level_14_; lean_object* v_hashes_15_; lean_object* v_content_16_; lean_object* v_closeHashes_x3f_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_25_; 
v_level_14_ = lean_ctor_get(v_block_3_, 0);
v_hashes_15_ = lean_ctor_get(v_block_3_, 1);
v_content_16_ = lean_ctor_get(v_block_3_, 2);
v_closeHashes_x3f_17_ = lean_ctor_get(v_block_3_, 3);
v_isSharedCheck_25_ = !lean_is_exclusive(v_block_3_);
if (v_isSharedCheck_25_ == 0)
{
v___x_19_ = v_block_3_;
v_isShared_20_ = v_isSharedCheck_25_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_closeHashes_x3f_17_);
lean_inc(v_content_16_);
lean_inc(v_hashes_15_);
lean_inc(v_level_14_);
lean_dec(v_block_3_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_25_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_21_; lean_object* v___x_23_; 
v___x_21_ = l_Lean_Markdown_parseInlines(v_s_1_, v_refs_2_, v_content_16_, v_extensions_4_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 2, v___x_21_);
v___x_23_ = v___x_19_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_level_14_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v_hashes_15_);
lean_ctor_set(v_reuseFailAlloc_24_, 2, v___x_21_);
lean_ctor_set(v_reuseFailAlloc_24_, 3, v_closeHashes_x3f_17_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
case 2:
{
lean_object* v_level_26_; lean_object* v_content_27_; lean_object* v_underline_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_36_; 
v_level_26_ = lean_ctor_get(v_block_3_, 0);
v_content_27_ = lean_ctor_get(v_block_3_, 1);
v_underline_28_ = lean_ctor_get(v_block_3_, 2);
v_isSharedCheck_36_ = !lean_is_exclusive(v_block_3_);
if (v_isSharedCheck_36_ == 0)
{
v___x_30_ = v_block_3_;
v_isShared_31_ = v_isSharedCheck_36_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_underline_28_);
lean_inc(v_content_27_);
lean_inc(v_level_26_);
lean_dec(v_block_3_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_36_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_32_; lean_object* v___x_34_; 
v___x_32_ = l_Lean_Markdown_parseInlines(v_s_1_, v_refs_2_, v_content_27_, v_extensions_4_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 1, v___x_32_);
v___x_34_ = v___x_30_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_level_26_);
lean_ctor_set(v_reuseFailAlloc_35_, 1, v___x_32_);
lean_ctor_set(v_reuseFailAlloc_35_, 2, v_underline_28_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
}
case 3:
{
lean_object* v_info_37_; lean_object* v_openFence_38_; lean_object* v_closeFence_x3f_39_; lean_object* v_lines_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_47_; 
lean_dec_ref(v_refs_2_);
lean_dec_ref(v_s_1_);
v_info_37_ = lean_ctor_get(v_block_3_, 0);
v_openFence_38_ = lean_ctor_get(v_block_3_, 1);
v_closeFence_x3f_39_ = lean_ctor_get(v_block_3_, 2);
v_lines_40_ = lean_ctor_get(v_block_3_, 3);
v_isSharedCheck_47_ = !lean_is_exclusive(v_block_3_);
if (v_isSharedCheck_47_ == 0)
{
v___x_42_ = v_block_3_;
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_lines_40_);
lean_inc(v_closeFence_x3f_39_);
lean_inc(v_openFence_38_);
lean_inc(v_info_37_);
lean_dec(v_block_3_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_45_; 
if (v_isShared_43_ == 0)
{
v___x_45_ = v___x_42_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_info_37_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v_openFence_38_);
lean_ctor_set(v_reuseFailAlloc_46_, 2, v_closeFence_x3f_39_);
lean_ctor_set(v_reuseFailAlloc_46_, 3, v_lines_40_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
case 4:
{
lean_object* v_lines_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_55_; 
lean_dec_ref(v_refs_2_);
lean_dec_ref(v_s_1_);
v_lines_48_ = lean_ctor_get(v_block_3_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v_block_3_);
if (v_isSharedCheck_55_ == 0)
{
v___x_50_ = v_block_3_;
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_lines_48_);
lean_dec(v_block_3_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_53_; 
if (v_isShared_51_ == 0)
{
v___x_53_ = v___x_50_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_lines_48_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
case 5:
{
lean_object* v_lines_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_63_; 
lean_dec_ref(v_refs_2_);
lean_dec_ref(v_s_1_);
v_lines_56_ = lean_ctor_get(v_block_3_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v_block_3_);
if (v_isSharedCheck_63_ == 0)
{
v___x_58_ = v_block_3_;
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_lines_56_);
lean_dec(v_block_3_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_61_; 
if (v_isShared_59_ == 0)
{
v___x_61_ = v___x_58_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_lines_56_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
case 6:
{
lean_object* v_markers_64_; lean_object* v_children_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_75_; 
v_markers_64_ = lean_ctor_get(v_block_3_, 0);
v_children_65_ = lean_ctor_get(v_block_3_, 1);
v_isSharedCheck_75_ = !lean_is_exclusive(v_block_3_);
if (v_isSharedCheck_75_ == 0)
{
v___x_67_ = v_block_3_;
v_isShared_68_ = v_isSharedCheck_75_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_children_65_);
lean_inc(v_markers_64_);
lean_dec(v_block_3_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_75_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
size_t v_sz_69_; size_t v___x_70_; lean_object* v___x_71_; lean_object* v___x_73_; 
v_sz_69_ = lean_array_size(v_children_65_);
v___x_70_ = ((size_t)0ULL);
v___x_71_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_parseInlinesInBlock_spec__0(v_s_1_, v_refs_2_, v_extensions_4_, v_sz_69_, v___x_70_, v_children_65_);
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 1, v___x_71_);
v___x_73_ = v___x_67_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_markers_64_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v___x_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
case 7:
{
lean_object* v_kind_76_; uint8_t v_tight_77_; lean_object* v_items_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_88_; 
v_kind_76_ = lean_ctor_get(v_block_3_, 0);
v_tight_77_ = lean_ctor_get_uint8(v_block_3_, sizeof(void*)*2);
v_items_78_ = lean_ctor_get(v_block_3_, 1);
v_isSharedCheck_88_ = !lean_is_exclusive(v_block_3_);
if (v_isSharedCheck_88_ == 0)
{
v___x_80_ = v_block_3_;
v_isShared_81_ = v_isSharedCheck_88_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_items_78_);
lean_inc(v_kind_76_);
lean_dec(v_block_3_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_88_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
size_t v_sz_82_; size_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v_sz_82_ = lean_array_size(v_items_78_);
v___x_83_ = ((size_t)0ULL);
v___x_84_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_parseInlinesInBlock_spec__0(v_s_1_, v_refs_2_, v_extensions_4_, v_sz_82_, v___x_83_, v_items_78_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 1, v___x_84_);
v___x_86_ = v___x_80_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(7, 2, 1);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_kind_76_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v___x_84_);
lean_ctor_set_uint8(v_reuseFailAlloc_87_, sizeof(void*)*2, v_tight_77_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
case 8:
{
lean_object* v_marker_89_; lean_object* v_children_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_100_; 
v_marker_89_ = lean_ctor_get(v_block_3_, 0);
v_children_90_ = lean_ctor_get(v_block_3_, 1);
v_isSharedCheck_100_ = !lean_is_exclusive(v_block_3_);
if (v_isSharedCheck_100_ == 0)
{
v___x_92_ = v_block_3_;
v_isShared_93_ = v_isSharedCheck_100_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_children_90_);
lean_inc(v_marker_89_);
lean_dec(v_block_3_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_100_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
size_t v_sz_94_; size_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_98_; 
v_sz_94_ = lean_array_size(v_children_90_);
v___x_95_ = ((size_t)0ULL);
v___x_96_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_parseInlinesInBlock_spec__0(v_s_1_, v_refs_2_, v_extensions_4_, v_sz_94_, v___x_95_, v_children_90_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 1, v___x_96_);
v___x_98_ = v___x_92_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_marker_89_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
case 9:
{
lean_object* v_m_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_108_; 
lean_dec_ref(v_refs_2_);
lean_dec_ref(v_s_1_);
v_m_101_ = lean_ctor_get(v_block_3_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v_block_3_);
if (v_isSharedCheck_108_ == 0)
{
v___x_103_ = v_block_3_;
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_m_101_);
lean_dec(v_block_3_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_m_101_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
default: 
{
lean_object* v_line_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_116_; 
lean_dec_ref(v_refs_2_);
lean_dec_ref(v_s_1_);
v_line_109_ = lean_ctor_get(v_block_3_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v_block_3_);
if (v_isSharedCheck_116_ == 0)
{
v___x_111_ = v_block_3_;
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_line_109_);
lean_dec(v_block_3_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_116_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_line_109_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_parseInlinesInBlock_spec__0(lean_object* v_s_117_, lean_object* v_refs_118_, uint8_t v_extensions_119_, size_t v_sz_120_, size_t v_i_121_, lean_object* v_bs_122_){
_start:
{
uint8_t v___x_123_; 
v___x_123_ = lean_usize_dec_lt(v_i_121_, v_sz_120_);
if (v___x_123_ == 0)
{
lean_dec_ref(v_refs_118_);
lean_dec_ref(v_s_117_);
return v_bs_122_;
}
else
{
lean_object* v_v_124_; lean_object* v___x_125_; lean_object* v_bs_x27_126_; lean_object* v___x_127_; size_t v___x_128_; size_t v___x_129_; lean_object* v___x_130_; 
v_v_124_ = lean_array_uget(v_bs_122_, v_i_121_);
v___x_125_ = lean_unsigned_to_nat(0u);
v_bs_x27_126_ = lean_array_uset(v_bs_122_, v_i_121_, v___x_125_);
lean_inc_ref(v_refs_118_);
lean_inc_ref(v_s_117_);
v___x_127_ = l_Lean_Markdown_parseInlinesInBlock(v_s_117_, v_refs_118_, v_v_124_, v_extensions_119_);
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_add(v_i_121_, v___x_128_);
v___x_130_ = lean_array_uset(v_bs_x27_126_, v_i_121_, v___x_127_);
v_i_121_ = v___x_129_;
v_bs_122_ = v___x_130_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_parseInlinesInBlock_spec__0___boxed(lean_object* v_s_132_, lean_object* v_refs_133_, lean_object* v_extensions_134_, lean_object* v_sz_135_, lean_object* v_i_136_, lean_object* v_bs_137_){
_start:
{
uint8_t v_extensions_boxed_138_; size_t v_sz_boxed_139_; size_t v_i_boxed_140_; lean_object* v_res_141_; 
v_extensions_boxed_138_ = lean_unbox(v_extensions_134_);
v_sz_boxed_139_ = lean_unbox_usize(v_sz_135_);
lean_dec(v_sz_135_);
v_i_boxed_140_ = lean_unbox_usize(v_i_136_);
lean_dec(v_i_136_);
v_res_141_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_parseInlinesInBlock_spec__0(v_s_132_, v_refs_133_, v_extensions_boxed_138_, v_sz_boxed_139_, v_i_boxed_140_, v_bs_137_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseInlinesInBlock___boxed(lean_object* v_s_142_, lean_object* v_refs_143_, lean_object* v_block_144_, lean_object* v_extensions_145_){
_start:
{
uint8_t v_extensions_boxed_146_; lean_object* v_res_147_; 
v_extensions_boxed_146_ = lean_unbox(v_extensions_145_);
v_res_147_ = l_Lean_Markdown_parseInlinesInBlock(v_s_142_, v_refs_143_, v_block_144_, v_extensions_boxed_146_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseDocument(lean_object* v_s_148_, lean_object* v_indent_149_, uint8_t v_extensions_150_, lean_object* v_externalRefs_151_){
_start:
{
lean_object* v_blocks_152_; lean_object* v_refs_153_; size_t v_sz_154_; size_t v___x_155_; lean_object* v___x_156_; 
v_blocks_152_ = l_Lean_Markdown_parseBlocks(v_s_148_, v_indent_149_);
v_refs_153_ = l_Lean_Markdown_buildRefTable(v_s_148_, v_blocks_152_, v_externalRefs_151_);
v_sz_154_ = lean_array_size(v_blocks_152_);
v___x_155_ = ((size_t)0ULL);
v___x_156_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Markdown_parseInlinesInBlock_spec__0(v_s_148_, v_refs_153_, v_extensions_150_, v_sz_154_, v___x_155_, v_blocks_152_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_parseDocument___boxed(lean_object* v_s_157_, lean_object* v_indent_158_, lean_object* v_extensions_159_, lean_object* v_externalRefs_160_){
_start:
{
uint8_t v_extensions_boxed_161_; lean_object* v_res_162_; 
v_extensions_boxed_161_ = lean_unbox(v_extensions_159_);
v_res_162_ = l_Lean_Markdown_parseDocument(v_s_157_, v_indent_158_, v_extensions_boxed_161_, v_externalRefs_160_);
lean_dec_ref(v_externalRefs_160_);
lean_dec(v_indent_158_);
return v_res_162_;
}
}
lean_object* runtime_initialize_Lean_Data_Markdown_Parser_Block(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Parser_Inline(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Markdown_Parser(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Markdown_Parser_Block(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Parser_Inline(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Markdown_Parser(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Markdown_Parser_Block(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Parser_Inline(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Markdown_Parser(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Markdown_Parser_Block(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Parser_Inline(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Markdown_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Markdown_Parser(builtin);
}
#ifdef __cplusplus
}
#endif
