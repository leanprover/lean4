// Lean compiler output
// Module: Lake.Toml.Load
// Imports: public import Lean.Parser.Types public import Lake.Toml.Data.Value import Lake.Toml.Elab import Lake.Util.Message import Std.Do
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Data_Trie_empty___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
extern lean_object* l_Lean_diagnostics;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkEmptyEnvironment(uint32_t);
extern lean_object* l_Lake_Toml_toml;
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_mkParserErrorMessage(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lake_Toml_elabToml(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* l_Lake_mkExceptionMessage(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lake_mkMessageNoPos(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Toml_loadToml___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_loadToml___closed__0;
static const lean_string_object l_Lake_Toml_loadToml___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_Toml_loadToml___closed__1 = (const lean_object*)&l_Lake_Toml_loadToml___closed__1_value;
static const lean_string_object l_Lake_Toml_loadToml___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "end of input"};
static const lean_object* l_Lake_Toml_loadToml___closed__2 = (const lean_object*)&l_Lake_Toml_loadToml___closed__2_value;
static const lean_ctor_object l_Lake_Toml_loadToml___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_loadToml___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_loadToml___closed__3 = (const lean_object*)&l_Lake_Toml_loadToml___closed__3_value;
static const lean_ctor_object l_Lake_Toml_loadToml___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Toml_loadToml___closed__1_value),((lean_object*)&l_Lake_Toml_loadToml___closed__3_value)}};
static const lean_object* l_Lake_Toml_loadToml___closed__4 = (const lean_object*)&l_Lake_Toml_loadToml___closed__4_value;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_loadToml___closed__5;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_loadToml___closed__6;
static const lean_string_object l_Lake_Toml_loadToml___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_Lake_Toml_loadToml___closed__7 = (const lean_object*)&l_Lake_Toml_loadToml___closed__7_value;
static const lean_ctor_object l_Lake_Toml_loadToml___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Toml_loadToml___closed__7_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_Lake_Toml_loadToml___closed__8 = (const lean_object*)&l_Lake_Toml_loadToml___closed__8_value;
static const lean_ctor_object l_Lake_Toml_loadToml___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Toml_loadToml___closed__8_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_Toml_loadToml___closed__9 = (const lean_object*)&l_Lake_Toml_loadToml___closed__9_value;
static const lean_ctor_object l_Lake_Toml_loadToml___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_loadToml___closed__10 = (const lean_object*)&l_Lake_Toml_loadToml___closed__10_value;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_loadToml___closed__11;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_loadToml___closed__12;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_loadToml___closed__13;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_loadToml___closed__14;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_loadToml___closed__15;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_loadToml___closed__16;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_loadToml___closed__17;
static const lean_array_object l_Lake_Toml_loadToml___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Toml_loadToml___closed__18 = (const lean_object*)&l_Lake_Toml_loadToml___closed__18_value;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_Toml_loadToml___closed__19;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_loadToml___closed__20;
static const lean_string_object l_Lake_Toml_loadToml___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "failed to initialize TOML environment: "};
static const lean_object* l_Lake_Toml_loadToml___closed__21 = (const lean_object*)&l_Lake_Toml_loadToml___closed__21_value;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_loadToml___closed__22;
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
uint8_t v___x_7_; 
v___x_7_ = lean_unbox(v_defValue_4_);
return v___x_7_;
}
else
{
lean_object* v_val_8_; 
v_val_8_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_8_);
lean_dec_ref_known(v___x_6_, 1);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref_known(v_val_8_, 0);
return v_v_9_;
}
else
{
uint8_t v___x_10_; 
lean_dec(v_val_8_);
v___x_10_ = lean_unbox(v_defValue_4_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0___boxed(lean_object* v_opts_11_, lean_object* v_opt_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(v_opts_11_, v_opt_12_);
lean_dec_ref(v_opt_12_);
lean_dec_ref(v_opts_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1(lean_object* v_opts_15_, lean_object* v_opt_16_){
_start:
{
lean_object* v_name_17_; lean_object* v_defValue_18_; lean_object* v_map_19_; lean_object* v___x_20_; 
v_name_17_ = lean_ctor_get(v_opt_16_, 0);
v_defValue_18_ = lean_ctor_get(v_opt_16_, 1);
v_map_19_ = lean_ctor_get(v_opts_15_, 0);
v___x_20_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_19_, v_name_17_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_inc(v_defValue_18_);
return v_defValue_18_;
}
else
{
lean_object* v_val_21_; 
v_val_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_val_21_);
lean_dec_ref_known(v___x_20_, 1);
if (lean_obj_tag(v_val_21_) == 3)
{
lean_object* v_v_22_; 
v_v_22_ = lean_ctor_get(v_val_21_, 0);
lean_inc(v_v_22_);
lean_dec_ref_known(v_val_21_, 1);
return v_v_22_;
}
else
{
lean_dec(v_val_21_);
lean_inc(v_defValue_18_);
return v_defValue_18_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1___boxed(lean_object* v_opts_23_, lean_object* v_opt_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1(v_opts_23_, v_opt_24_);
lean_dec_ref(v_opt_24_);
lean_dec_ref(v_opts_23_);
return v_res_25_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__0(void){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_Data_Trie_empty___redArg();
return v___x_26_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__5(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = l_Lean_Options_empty;
v___x_37_ = l_Lean_Core_getMaxHeartbeats(v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__6(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_unsigned_to_nat(1u);
v___x_39_ = l_Lean_firstFrontendMacroScope;
v___x_40_ = lean_nat_add(v___x_39_, v___x_38_);
return v___x_40_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__11(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_unsigned_to_nat(32u);
v___x_52_ = lean_mk_empty_array_with_capacity(v___x_51_);
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__12(void){
_start:
{
size_t v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_54_ = ((size_t)5ULL);
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = lean_unsigned_to_nat(32u);
v___x_57_ = lean_mk_empty_array_with_capacity(v___x_56_);
v___x_58_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__11, &l_Lake_Toml_loadToml___closed__11_once, _init_l_Lake_Toml_loadToml___closed__11);
v___x_59_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
lean_ctor_set(v___x_59_, 2, v___x_55_);
lean_ctor_set(v___x_59_, 3, v___x_55_);
lean_ctor_set_usize(v___x_59_, 4, v___x_54_);
return v___x_59_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__13(void){
_start:
{
lean_object* v___x_60_; uint64_t v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__12, &l_Lake_Toml_loadToml___closed__12_once, _init_l_Lake_Toml_loadToml___closed__12);
v___x_61_ = 0ULL;
v___x_62_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_62_, 0, v___x_60_);
lean_ctor_set_uint64(v___x_62_, sizeof(void*)*1, v___x_61_);
return v___x_62_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__14(void){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_63_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__15(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__14, &l_Lake_Toml_loadToml___closed__14_once, _init_l_Lake_Toml_loadToml___closed__14);
v___x_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
return v___x_65_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__16(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__15, &l_Lake_Toml_loadToml___closed__15_once, _init_l_Lake_Toml_loadToml___closed__15);
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
return v___x_67_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__17(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = l_Lean_NameSet_empty;
v___x_69_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__12, &l_Lake_Toml_loadToml___closed__12_once, _init_l_Lake_Toml_loadToml___closed__12);
v___x_70_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
lean_ctor_set(v___x_70_, 2, v___x_68_);
return v___x_70_;
}
}
static uint8_t _init_l_Lake_Toml_loadToml___closed__19(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_73_ = l_Lean_diagnostics;
v___x_74_ = l_Lean_Options_empty;
v___x_75_ = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(v___x_74_, v___x_73_);
return v___x_75_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__20(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = l_Lean_maxRecDepth;
v___x_77_ = l_Lean_Options_empty;
v___x_78_ = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__1(v___x_77_, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__22(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = ((lean_object*)(l_Lake_Toml_loadToml___closed__21));
v___x_81_ = l_Lean_stringToMessageData(v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object* v_ictx_82_){
_start:
{
lean_object* v___x_84_; uint32_t v___x_85_; lean_object* v___x_86_; 
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = 0;
v___x_86_ = l_Lean_mkEmptyEnvironment(v___x_85_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_197_; 
v_a_87_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_197_ == 0)
{
v___x_89_ = v___x_86_;
v_isShared_90_ = v_isSharedCheck_197_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_86_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_197_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v_fn_92_; lean_object* v_inputString_93_; lean_object* v_fileName_94_; lean_object* v_fileMap_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v_errorMsg_103_; 
v___x_91_ = l_Lake_Toml_toml;
v_fn_92_ = lean_ctor_get(v___x_91_, 1);
v_inputString_93_ = lean_ctor_get(v_ictx_82_, 0);
v_fileName_94_ = lean_ctor_get(v_ictx_82_, 1);
v_fileMap_95_ = lean_ctor_get(v_ictx_82_, 2);
v___x_96_ = l_Lean_Options_empty;
v___x_97_ = lean_box(0);
v___x_98_ = lean_box(0);
lean_inc(v_a_87_);
v___x_99_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_99_, 0, v_a_87_);
lean_ctor_set(v___x_99_, 1, v___x_96_);
lean_ctor_set(v___x_99_, 2, v___x_97_);
lean_ctor_set(v___x_99_, 3, v___x_98_);
v___x_100_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__0, &l_Lake_Toml_loadToml___closed__0_once, _init_l_Lake_Toml_loadToml___closed__0);
v___x_101_ = l_Lean_Parser_mkParserState(v_inputString_93_);
lean_inc_ref(v_ictx_82_);
lean_inc_ref(v_fn_92_);
v___x_102_ = l_Lean_Parser_ParserFn_run(v_fn_92_, v_ictx_82_, v___x_99_, v___x_100_, v___x_101_);
v_errorMsg_103_ = lean_ctor_get(v___x_102_, 4);
lean_inc(v_errorMsg_103_);
if (lean_obj_tag(v_errorMsg_103_) == 1)
{
lean_object* v_val_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
lean_dec(v_a_87_);
v_val_104_ = lean_ctor_get(v_errorMsg_103_, 0);
lean_inc(v_val_104_);
lean_dec_ref_known(v_errorMsg_103_, 1);
v___x_105_ = l_Lake_mkParserErrorMessage(v_ictx_82_, v___x_102_, v_val_104_);
lean_dec_ref(v___x_102_);
v___x_106_ = l_Lean_MessageLog_empty;
v___x_107_ = l_Lean_MessageLog_add(v___x_105_, v___x_106_);
if (v_isShared_90_ == 0)
{
lean_ctor_set_tag(v___x_89_, 1);
lean_ctor_set(v___x_89_, 0, v___x_107_);
v___x_109_ = v___x_89_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
else
{
lean_object* v_stxStack_111_; lean_object* v_pos_112_; uint8_t v___x_113_; 
lean_dec(v_errorMsg_103_);
v_stxStack_111_ = lean_ctor_get(v___x_102_, 0);
lean_inc_ref(v_stxStack_111_);
v_pos_112_ = lean_ctor_get(v___x_102_, 2);
lean_inc(v_pos_112_);
v___x_113_ = l_Lean_Parser_InputContext_atEnd(v_ictx_82_, v_pos_112_);
lean_dec(v_pos_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_119_; 
lean_dec_ref(v_stxStack_111_);
lean_dec(v_a_87_);
v___x_114_ = ((lean_object*)(l_Lake_Toml_loadToml___closed__4));
v___x_115_ = l_Lake_mkParserErrorMessage(v_ictx_82_, v___x_102_, v___x_114_);
lean_dec_ref(v___x_102_);
v___x_116_ = l_Lean_MessageLog_empty;
v___x_117_ = l_Lean_MessageLog_add(v___x_115_, v___x_116_);
if (v_isShared_90_ == 0)
{
lean_ctor_set_tag(v___x_89_, 1);
lean_ctor_set(v___x_89_, 0, v___x_117_);
v___x_119_ = v___x_89_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
else
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; lean_object* v___y_143_; lean_object* v___x_173_; uint8_t v___y_175_; lean_object* v_env_195_; uint8_t v___x_196_; 
lean_dec_ref(v___x_102_);
lean_del_object(v___x_89_);
v___x_121_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_111_);
lean_dec_ref(v_stxStack_111_);
v___x_122_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__5, &l_Lake_Toml_loadToml___closed__5_once, _init_l_Lake_Toml_loadToml___closed__5);
v___x_123_ = l_Lean_firstFrontendMacroScope;
v___x_124_ = lean_box(0);
v___x_125_ = lean_box(0);
v___x_126_ = 0;
v___x_127_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__6, &l_Lake_Toml_loadToml___closed__6_once, _init_l_Lake_Toml_loadToml___closed__6);
v___x_128_ = ((lean_object*)(l_Lake_Toml_loadToml___closed__9));
v___x_129_ = ((lean_object*)(l_Lake_Toml_loadToml___closed__10));
v___x_130_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__12, &l_Lake_Toml_loadToml___closed__12_once, _init_l_Lake_Toml_loadToml___closed__12);
v___x_131_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__13, &l_Lake_Toml_loadToml___closed__13_once, _init_l_Lake_Toml_loadToml___closed__13);
v___x_132_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__15, &l_Lake_Toml_loadToml___closed__15_once, _init_l_Lake_Toml_loadToml___closed__15);
v___x_133_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__16, &l_Lake_Toml_loadToml___closed__16_once, _init_l_Lake_Toml_loadToml___closed__16);
v___x_134_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__17, &l_Lake_Toml_loadToml___closed__17_once, _init_l_Lake_Toml_loadToml___closed__17);
v___x_135_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_135_, 0, v___x_132_);
lean_ctor_set(v___x_135_, 1, v___x_132_);
lean_ctor_set(v___x_135_, 2, v___x_130_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*3, v___x_113_);
v___x_136_ = ((lean_object*)(l_Lake_Toml_loadToml___closed__18));
v___x_137_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_137_, 0, v_a_87_);
lean_ctor_set(v___x_137_, 1, v___x_127_);
lean_ctor_set(v___x_137_, 2, v___x_128_);
lean_ctor_set(v___x_137_, 3, v___x_129_);
lean_ctor_set(v___x_137_, 4, v___x_131_);
lean_ctor_set(v___x_137_, 5, v___x_133_);
lean_ctor_set(v___x_137_, 6, v___x_134_);
lean_ctor_set(v___x_137_, 7, v___x_135_);
lean_ctor_set(v___x_137_, 8, v___x_136_);
v___x_138_ = lean_st_mk_ref(v___x_137_);
v___x_139_ = l_Lean_inheritedTraceOptions;
v___x_140_ = lean_st_ref_get(v___x_139_);
v___x_141_ = lean_uint8_once(&l_Lake_Toml_loadToml___closed__19, &l_Lake_Toml_loadToml___closed__19_once, _init_l_Lake_Toml_loadToml___closed__19);
v___x_173_ = lean_st_ref_get(v___x_138_);
v_env_195_ = lean_ctor_get(v___x_173_, 0);
lean_inc_ref(v_env_195_);
lean_dec(v___x_173_);
v___x_196_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_195_);
lean_dec_ref(v_env_195_);
if (v___x_141_ == 0)
{
if (v___x_196_ == 0)
{
v___y_175_ = v___x_113_;
goto v___jp_174_;
}
else
{
v___y_175_ = v___x_141_;
goto v___jp_174_;
}
}
else
{
v___y_175_ = v___x_196_;
goto v___jp_174_;
}
v___jp_142_:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_144_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__20, &l_Lake_Toml_loadToml___closed__20_once, _init_l_Lake_Toml_loadToml___closed__20);
lean_inc_ref(v_fileMap_95_);
lean_inc_ref(v_fileName_94_);
v___x_145_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_145_, 0, v_fileName_94_);
lean_ctor_set(v___x_145_, 1, v_fileMap_95_);
lean_ctor_set(v___x_145_, 2, v___x_96_);
lean_ctor_set(v___x_145_, 3, v___x_144_);
lean_ctor_set(v___x_145_, 4, v___x_97_);
lean_ctor_set(v___x_145_, 5, v___x_98_);
lean_ctor_set(v___x_145_, 6, v___x_84_);
lean_ctor_set(v___x_145_, 7, v___x_122_);
lean_ctor_set(v___x_145_, 8, v___x_97_);
lean_ctor_set(v___x_145_, 9, v___x_123_);
lean_ctor_set(v___x_145_, 10, v___x_124_);
lean_ctor_set(v___x_145_, 11, v___x_140_);
v___x_146_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_146_, 0, v___x_145_);
lean_ctor_set(v___x_146_, 1, v___x_84_);
lean_ctor_set(v___x_146_, 2, v___x_125_);
lean_ctor_set_uint8(v___x_146_, sizeof(void*)*3, v___x_141_);
lean_ctor_set_uint8(v___x_146_, sizeof(void*)*3 + 1, v___x_126_);
v___x_147_ = l_Lake_Toml_elabToml(v___x_121_, v___x_146_, v___y_143_);
lean_dec(v___y_143_);
lean_dec_ref_known(v___x_146_, 3);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_161_; 
lean_dec_ref(v_ictx_82_);
v_a_148_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_161_ == 0)
{
v___x_150_ = v___x_147_;
v_isShared_151_ = v_isSharedCheck_161_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_147_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_161_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; lean_object* v_messages_153_; uint8_t v___x_154_; 
v___x_152_ = lean_st_ref_get(v___x_138_);
lean_dec(v___x_138_);
v_messages_153_ = lean_ctor_get(v___x_152_, 6);
lean_inc_ref(v_messages_153_);
lean_dec(v___x_152_);
v___x_154_ = l_Lean_MessageLog_hasErrors(v_messages_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_156_; 
lean_dec_ref(v_messages_153_);
if (v_isShared_151_ == 0)
{
v___x_156_ = v___x_150_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_148_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
else
{
lean_object* v___x_159_; 
lean_dec(v_a_148_);
if (v_isShared_151_ == 0)
{
lean_ctor_set_tag(v___x_150_, 1);
lean_ctor_set(v___x_150_, 0, v_messages_153_);
v___x_159_ = v___x_150_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_messages_153_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_172_; 
lean_dec(v___x_138_);
v_a_162_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_172_ == 0)
{
v___x_164_ = v___x_147_;
v_isShared_165_ = v_isSharedCheck_172_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_147_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_172_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_166_ = l_Lake_mkExceptionMessage(v_ictx_82_, v_a_162_);
v___x_167_ = l_Lean_MessageLog_empty;
v___x_168_ = l_Lean_MessageLog_add(v___x_166_, v___x_167_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_168_);
v___x_170_ = v___x_164_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
v___jp_174_:
{
if (v___y_175_ == 0)
{
lean_object* v___x_176_; lean_object* v_env_177_; lean_object* v_nextMacroScope_178_; lean_object* v_ngen_179_; lean_object* v_auxDeclNGen_180_; lean_object* v_traceState_181_; lean_object* v_messages_182_; lean_object* v_infoState_183_; lean_object* v_snapshotTasks_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_193_; 
v___x_176_ = lean_st_ref_take(v___x_138_);
v_env_177_ = lean_ctor_get(v___x_176_, 0);
v_nextMacroScope_178_ = lean_ctor_get(v___x_176_, 1);
v_ngen_179_ = lean_ctor_get(v___x_176_, 2);
v_auxDeclNGen_180_ = lean_ctor_get(v___x_176_, 3);
v_traceState_181_ = lean_ctor_get(v___x_176_, 4);
v_messages_182_ = lean_ctor_get(v___x_176_, 6);
v_infoState_183_ = lean_ctor_get(v___x_176_, 7);
v_snapshotTasks_184_ = lean_ctor_get(v___x_176_, 8);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_193_ == 0)
{
lean_object* v_unused_194_; 
v_unused_194_ = lean_ctor_get(v___x_176_, 5);
lean_dec(v_unused_194_);
v___x_186_ = v___x_176_;
v_isShared_187_ = v_isSharedCheck_193_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_snapshotTasks_184_);
lean_inc(v_infoState_183_);
lean_inc(v_messages_182_);
lean_inc(v_traceState_181_);
lean_inc(v_auxDeclNGen_180_);
lean_inc(v_ngen_179_);
lean_inc(v_nextMacroScope_178_);
lean_inc(v_env_177_);
lean_dec(v___x_176_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_193_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_188_ = l_Lean_Kernel_enableDiag(v_env_177_, v___x_141_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 5, v___x_133_);
lean_ctor_set(v___x_186_, 0, v___x_188_);
v___x_190_ = v___x_186_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v_nextMacroScope_178_);
lean_ctor_set(v_reuseFailAlloc_192_, 2, v_ngen_179_);
lean_ctor_set(v_reuseFailAlloc_192_, 3, v_auxDeclNGen_180_);
lean_ctor_set(v_reuseFailAlloc_192_, 4, v_traceState_181_);
lean_ctor_set(v_reuseFailAlloc_192_, 5, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_192_, 6, v_messages_182_);
lean_ctor_set(v_reuseFailAlloc_192_, 7, v_infoState_183_);
lean_ctor_set(v_reuseFailAlloc_192_, 8, v_snapshotTasks_184_);
v___x_190_ = v_reuseFailAlloc_192_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; 
v___x_191_ = lean_st_ref_put(v___x_138_, v___x_190_);
lean_inc(v___x_138_);
v___y_143_ = v___x_138_;
goto v___jp_142_;
}
}
}
else
{
lean_inc(v___x_138_);
v___y_143_ = v___x_138_;
goto v___jp_142_;
}
}
}
}
}
}
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_214_; 
v_a_198_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_214_ == 0)
{
v___x_200_ = v___x_86_;
v_isShared_201_ = v_isSharedCheck_214_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_86_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_214_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_202_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__22, &l_Lake_Toml_loadToml___closed__22_once, _init_l_Lake_Toml_loadToml___closed__22);
v___x_203_ = lean_io_error_to_string(v_a_198_);
v___x_204_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
v___x_205_ = l_Lean_MessageData_ofFormat(v___x_204_);
v___x_206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_202_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = 2;
v___x_208_ = l_Lake_mkMessageNoPos(v_ictx_82_, v___x_206_, v___x_207_);
v___x_209_ = l_Lean_MessageLog_empty;
v___x_210_ = l_Lean_MessageLog_add(v___x_208_, v___x_209_);
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 0, v___x_210_);
v___x_212_ = v___x_200_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_210_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml___boxed(lean_object* v_ictx_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lake_Toml_loadToml(v_ictx_215_);
return v_res_217_;
}
}
lean_object* runtime_initialize_Lean_Parser_Types(uint8_t builtin);
lean_object* runtime_initialize_Lake_Toml_Data_Value(uint8_t builtin);
lean_object* runtime_initialize_Lake_Toml_Elab(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Message(uint8_t builtin);
lean_object* runtime_initialize_Std_Do(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_Load(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean_Parser_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Toml_Data_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Toml_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Toml_Load(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Types(uint8_t builtin);
lean_object* initialize_Lake_Toml_Data_Value(uint8_t builtin);
lean_object* initialize_Lake_Toml_Elab(uint8_t builtin);
lean_object* initialize_Lake_Util_Message(uint8_t builtin);
lean_object* initialize_Std_Do(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Load(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Data_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Toml_Load(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Toml_Load(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Toml_Load(builtin);
}
#ifdef __cplusplus
}
#endif
