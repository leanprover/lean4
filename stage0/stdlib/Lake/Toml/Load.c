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
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Data_Trie_empty(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_environment(uint32_t);
extern lean_object* l_Lake_Toml_toml;
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_mkParserErrorMessage(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lake_Toml_elabToml(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* l_Lake_mkExceptionMessage(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
static const lean_string_object l_Lake_Toml_loadToml___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_Lake_Toml_loadToml___closed__6 = (const lean_object*)&l_Lake_Toml_loadToml___closed__6_value;
static const lean_ctor_object l_Lake_Toml_loadToml___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Toml_loadToml___closed__6_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_Lake_Toml_loadToml___closed__7 = (const lean_object*)&l_Lake_Toml_loadToml___closed__7_value;
static const lean_ctor_object l_Lake_Toml_loadToml___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Toml_loadToml___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_Toml_loadToml___closed__8 = (const lean_object*)&l_Lake_Toml_loadToml___closed__8_value;
static const lean_ctor_object l_Lake_Toml_loadToml___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_loadToml___closed__9 = (const lean_object*)&l_Lake_Toml_loadToml___closed__9_value;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_loadToml___closed__10;
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
static const lean_array_object l_Lake_Toml_loadToml___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Toml_loadToml___closed__17 = (const lean_object*)&l_Lake_Toml_loadToml___closed__17_value;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_loadToml___closed__18;
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
lean_dec_ref(v___x_6_);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref(v_val_8_);
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
lean_dec_ref(v___x_20_);
if (lean_obj_tag(v_val_21_) == 3)
{
lean_object* v_v_22_; 
v_v_22_ = lean_ctor_get(v_val_21_, 0);
lean_inc(v_v_22_);
lean_dec_ref(v_val_21_);
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
v___x_26_ = l_Lean_Data_Trie_empty(lean_box(0));
return v___x_26_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__5(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = lean_unsigned_to_nat(1u);
v___x_37_ = l_Lean_firstFrontendMacroScope;
v___x_38_ = lean_nat_add(v___x_37_, v___x_36_);
return v___x_38_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__10(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_unsigned_to_nat(32u);
v___x_50_ = lean_mk_empty_array_with_capacity(v___x_49_);
v___x_51_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__11(void){
_start:
{
size_t v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_52_ = ((size_t)5ULL);
v___x_53_ = lean_unsigned_to_nat(0u);
v___x_54_ = lean_unsigned_to_nat(32u);
v___x_55_ = lean_mk_empty_array_with_capacity(v___x_54_);
v___x_56_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__10, &l_Lake_Toml_loadToml___closed__10_once, _init_l_Lake_Toml_loadToml___closed__10);
v___x_57_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
lean_ctor_set(v___x_57_, 2, v___x_53_);
lean_ctor_set(v___x_57_, 3, v___x_53_);
lean_ctor_set_usize(v___x_57_, 4, v___x_52_);
return v___x_57_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__12(void){
_start:
{
lean_object* v___x_58_; uint64_t v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__11, &l_Lake_Toml_loadToml___closed__11_once, _init_l_Lake_Toml_loadToml___closed__11);
v___x_59_ = 0ULL;
v___x_60_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set_uint64(v___x_60_, sizeof(void*)*1, v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__13(void){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_61_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__14(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__13, &l_Lake_Toml_loadToml___closed__13_once, _init_l_Lake_Toml_loadToml___closed__13);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__15(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__14, &l_Lake_Toml_loadToml___closed__14_once, _init_l_Lake_Toml_loadToml___closed__14);
v___x_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
return v___x_65_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__16(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = l_Lean_NameSet_empty;
v___x_67_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__11, &l_Lake_Toml_loadToml___closed__11_once, _init_l_Lake_Toml_loadToml___closed__11);
v___x_68_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
lean_ctor_set(v___x_68_, 2, v___x_66_);
return v___x_68_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__18(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = l_Lean_Options_empty;
v___x_72_ = l_Lean_Core_getMaxHeartbeats(v___x_71_);
return v___x_72_;
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
uint32_t v___x_84_; lean_object* v___x_85_; 
v___x_84_ = 0;
v___x_85_ = lean_mk_empty_environment(v___x_84_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_209_; 
v_a_86_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_209_ == 0)
{
v___x_88_ = v___x_85_;
v_isShared_89_ = v_isSharedCheck_209_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_85_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_209_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; lean_object* v_fn_91_; lean_object* v_inputString_92_; lean_object* v_fileName_93_; lean_object* v_fileMap_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v_errorMsg_102_; 
v___x_90_ = l_Lake_Toml_toml;
v_fn_91_ = lean_ctor_get(v___x_90_, 1);
lean_inc_ref(v_fn_91_);
v_inputString_92_ = lean_ctor_get(v_ictx_82_, 0);
v_fileName_93_ = lean_ctor_get(v_ictx_82_, 1);
v_fileMap_94_ = lean_ctor_get(v_ictx_82_, 2);
v___x_95_ = l_Lean_Options_empty;
v___x_96_ = lean_box(0);
v___x_97_ = lean_box(0);
lean_inc(v_a_86_);
v___x_98_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_98_, 0, v_a_86_);
lean_ctor_set(v___x_98_, 1, v___x_95_);
lean_ctor_set(v___x_98_, 2, v___x_96_);
lean_ctor_set(v___x_98_, 3, v___x_97_);
v___x_99_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__0, &l_Lake_Toml_loadToml___closed__0_once, _init_l_Lake_Toml_loadToml___closed__0);
v___x_100_ = l_Lean_Parser_mkParserState(v_inputString_92_);
lean_inc_ref(v_ictx_82_);
v___x_101_ = l_Lean_Parser_ParserFn_run(v_fn_91_, v_ictx_82_, v___x_98_, v___x_99_, v___x_100_);
v_errorMsg_102_ = lean_ctor_get(v___x_101_, 4);
lean_inc(v_errorMsg_102_);
if (lean_obj_tag(v_errorMsg_102_) == 1)
{
lean_object* v_val_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_108_; 
lean_dec(v_a_86_);
v_val_103_ = lean_ctor_get(v_errorMsg_102_, 0);
lean_inc(v_val_103_);
lean_dec_ref(v_errorMsg_102_);
v___x_104_ = l_Lake_mkParserErrorMessage(v_ictx_82_, v___x_101_, v_val_103_);
lean_dec_ref(v___x_101_);
v___x_105_ = l_Lean_MessageLog_empty;
v___x_106_ = l_Lean_MessageLog_add(v___x_104_, v___x_105_);
if (v_isShared_89_ == 0)
{
lean_ctor_set_tag(v___x_88_, 1);
lean_ctor_set(v___x_88_, 0, v___x_106_);
v___x_108_ = v___x_88_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_106_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
else
{
lean_object* v_stxStack_110_; lean_object* v_pos_111_; uint8_t v___x_112_; 
lean_dec(v_errorMsg_102_);
v_stxStack_110_ = lean_ctor_get(v___x_101_, 0);
lean_inc_ref(v_stxStack_110_);
v_pos_111_ = lean_ctor_get(v___x_101_, 2);
lean_inc(v_pos_111_);
v___x_112_ = l_Lean_Parser_InputContext_atEnd(v_ictx_82_, v_pos_111_);
lean_dec(v_pos_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_118_; 
lean_dec_ref(v_stxStack_110_);
lean_dec(v_a_86_);
v___x_113_ = ((lean_object*)(l_Lake_Toml_loadToml___closed__4));
v___x_114_ = l_Lake_mkParserErrorMessage(v_ictx_82_, v___x_101_, v___x_113_);
lean_dec_ref(v___x_101_);
v___x_115_ = l_Lean_MessageLog_empty;
v___x_116_ = l_Lean_MessageLog_add(v___x_114_, v___x_115_);
if (v_isShared_89_ == 0)
{
lean_ctor_set_tag(v___x_88_, 1);
lean_ctor_set(v___x_88_, 0, v___x_116_);
v___x_118_ = v___x_88_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v_env_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; lean_object* v_fileName_145_; lean_object* v_fileMap_146_; lean_object* v_currRecDepth_147_; lean_object* v_ref_148_; lean_object* v_currNamespace_149_; lean_object* v_openDecls_150_; lean_object* v_initHeartbeats_151_; lean_object* v_maxHeartbeats_152_; lean_object* v_quotContext_153_; lean_object* v_currMacroScope_154_; lean_object* v_cancelTk_x3f_155_; uint8_t v_suppressElabErrors_156_; lean_object* v_inheritedTraceOptions_157_; lean_object* v___y_158_; uint8_t v___y_188_; uint8_t v___x_208_; 
lean_dec_ref(v___x_101_);
lean_del_object(v___x_88_);
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = l_Lean_firstFrontendMacroScope;
v___x_122_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__5, &l_Lake_Toml_loadToml___closed__5_once, _init_l_Lake_Toml_loadToml___closed__5);
v___x_123_ = ((lean_object*)(l_Lake_Toml_loadToml___closed__8));
v___x_124_ = ((lean_object*)(l_Lake_Toml_loadToml___closed__9));
v___x_125_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__11, &l_Lake_Toml_loadToml___closed__11_once, _init_l_Lake_Toml_loadToml___closed__11);
v___x_126_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__12, &l_Lake_Toml_loadToml___closed__12_once, _init_l_Lake_Toml_loadToml___closed__12);
v___x_127_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__14, &l_Lake_Toml_loadToml___closed__14_once, _init_l_Lake_Toml_loadToml___closed__14);
v___x_128_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__15, &l_Lake_Toml_loadToml___closed__15_once, _init_l_Lake_Toml_loadToml___closed__15);
v___x_129_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__16, &l_Lake_Toml_loadToml___closed__16_once, _init_l_Lake_Toml_loadToml___closed__16);
v___x_130_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_130_, 0, v___x_127_);
lean_ctor_set(v___x_130_, 1, v___x_127_);
lean_ctor_set(v___x_130_, 2, v___x_125_);
lean_ctor_set_uint8(v___x_130_, sizeof(void*)*3, v___x_112_);
v___x_131_ = ((lean_object*)(l_Lake_Toml_loadToml___closed__17));
v___x_132_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_132_, 0, v_a_86_);
lean_ctor_set(v___x_132_, 1, v___x_122_);
lean_ctor_set(v___x_132_, 2, v___x_123_);
lean_ctor_set(v___x_132_, 3, v___x_124_);
lean_ctor_set(v___x_132_, 4, v___x_126_);
lean_ctor_set(v___x_132_, 5, v___x_128_);
lean_ctor_set(v___x_132_, 6, v___x_129_);
lean_ctor_set(v___x_132_, 7, v___x_130_);
lean_ctor_set(v___x_132_, 8, v___x_131_);
v___x_133_ = lean_st_mk_ref(v___x_132_);
v___x_134_ = l_Lean_inheritedTraceOptions;
v___x_135_ = lean_st_ref_get(v___x_134_);
v___x_136_ = lean_st_ref_get(v___x_133_);
v_env_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc_ref(v_env_137_);
lean_dec(v___x_136_);
v___x_138_ = lean_box(0);
v___x_139_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__18, &l_Lake_Toml_loadToml___closed__18_once, _init_l_Lake_Toml_loadToml___closed__18);
v___x_140_ = 0;
v___x_141_ = lean_box(0);
v___x_142_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_110_);
lean_dec_ref(v_stxStack_110_);
v___x_143_ = lean_uint8_once(&l_Lake_Toml_loadToml___closed__19, &l_Lake_Toml_loadToml___closed__19_once, _init_l_Lake_Toml_loadToml___closed__19);
v___x_208_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_137_);
lean_dec_ref(v_env_137_);
if (v___x_208_ == 0)
{
if (v___x_143_ == 0)
{
v___y_188_ = v___x_112_;
goto v___jp_187_;
}
else
{
v___y_188_ = v___x_208_;
goto v___jp_187_;
}
}
else
{
v___y_188_ = v___x_143_;
goto v___jp_187_;
}
v___jp_144_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__20, &l_Lake_Toml_loadToml___closed__20_once, _init_l_Lake_Toml_loadToml___closed__20);
v___x_160_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_160_, 0, v_fileName_145_);
lean_ctor_set(v___x_160_, 1, v_fileMap_146_);
lean_ctor_set(v___x_160_, 2, v___x_95_);
lean_ctor_set(v___x_160_, 3, v_currRecDepth_147_);
lean_ctor_set(v___x_160_, 4, v___x_159_);
lean_ctor_set(v___x_160_, 5, v_ref_148_);
lean_ctor_set(v___x_160_, 6, v_currNamespace_149_);
lean_ctor_set(v___x_160_, 7, v_openDecls_150_);
lean_ctor_set(v___x_160_, 8, v_initHeartbeats_151_);
lean_ctor_set(v___x_160_, 9, v_maxHeartbeats_152_);
lean_ctor_set(v___x_160_, 10, v_quotContext_153_);
lean_ctor_set(v___x_160_, 11, v_currMacroScope_154_);
lean_ctor_set(v___x_160_, 12, v_cancelTk_x3f_155_);
lean_ctor_set(v___x_160_, 13, v_inheritedTraceOptions_157_);
lean_ctor_set_uint8(v___x_160_, sizeof(void*)*14, v___x_143_);
lean_ctor_set_uint8(v___x_160_, sizeof(void*)*14 + 1, v_suppressElabErrors_156_);
v___x_161_ = l_Lake_Toml_elabToml(v___x_142_, v___x_160_, v___y_158_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_175_; 
lean_dec_ref(v_ictx_82_);
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_175_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_175_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_175_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v_messages_167_; uint8_t v___x_168_; 
v___x_166_ = lean_st_ref_get(v___x_133_);
lean_dec(v___x_133_);
v_messages_167_ = lean_ctor_get(v___x_166_, 6);
lean_inc_ref(v_messages_167_);
lean_dec(v___x_166_);
v___x_168_ = l_Lean_MessageLog_hasErrors(v_messages_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_170_; 
lean_dec_ref(v_messages_167_);
if (v_isShared_165_ == 0)
{
v___x_170_ = v___x_164_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_162_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
else
{
lean_object* v___x_173_; 
lean_dec(v_a_162_);
if (v_isShared_165_ == 0)
{
lean_ctor_set_tag(v___x_164_, 1);
lean_ctor_set(v___x_164_, 0, v_messages_167_);
v___x_173_ = v___x_164_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_messages_167_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
else
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_186_; 
lean_dec(v___x_133_);
v_a_176_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_186_ == 0)
{
v___x_178_ = v___x_161_;
v_isShared_179_ = v_isSharedCheck_186_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_161_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_186_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_184_; 
v___x_180_ = l_Lake_mkExceptionMessage(v_ictx_82_, v_a_176_);
v___x_181_ = l_Lean_MessageLog_empty;
v___x_182_ = l_Lean_MessageLog_add(v___x_180_, v___x_181_);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_182_);
v___x_184_ = v___x_178_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
v___jp_187_:
{
if (v___y_188_ == 0)
{
lean_object* v___x_189_; lean_object* v_env_190_; lean_object* v_nextMacroScope_191_; lean_object* v_ngen_192_; lean_object* v_auxDeclNGen_193_; lean_object* v_traceState_194_; lean_object* v_messages_195_; lean_object* v_infoState_196_; lean_object* v_snapshotTasks_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_206_; 
v___x_189_ = lean_st_ref_take(v___x_133_);
v_env_190_ = lean_ctor_get(v___x_189_, 0);
v_nextMacroScope_191_ = lean_ctor_get(v___x_189_, 1);
v_ngen_192_ = lean_ctor_get(v___x_189_, 2);
v_auxDeclNGen_193_ = lean_ctor_get(v___x_189_, 3);
v_traceState_194_ = lean_ctor_get(v___x_189_, 4);
v_messages_195_ = lean_ctor_get(v___x_189_, 6);
v_infoState_196_ = lean_ctor_get(v___x_189_, 7);
v_snapshotTasks_197_ = lean_ctor_get(v___x_189_, 8);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_206_ == 0)
{
lean_object* v_unused_207_; 
v_unused_207_ = lean_ctor_get(v___x_189_, 5);
lean_dec(v_unused_207_);
v___x_199_ = v___x_189_;
v_isShared_200_ = v_isSharedCheck_206_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_snapshotTasks_197_);
lean_inc(v_infoState_196_);
lean_inc(v_messages_195_);
lean_inc(v_traceState_194_);
lean_inc(v_auxDeclNGen_193_);
lean_inc(v_ngen_192_);
lean_inc(v_nextMacroScope_191_);
lean_inc(v_env_190_);
lean_dec(v___x_189_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_206_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_201_ = l_Lean_Kernel_enableDiag(v_env_190_, v___x_143_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 5, v___x_128_);
lean_ctor_set(v___x_199_, 0, v___x_201_);
v___x_203_ = v___x_199_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_nextMacroScope_191_);
lean_ctor_set(v_reuseFailAlloc_205_, 2, v_ngen_192_);
lean_ctor_set(v_reuseFailAlloc_205_, 3, v_auxDeclNGen_193_);
lean_ctor_set(v_reuseFailAlloc_205_, 4, v_traceState_194_);
lean_ctor_set(v_reuseFailAlloc_205_, 5, v___x_128_);
lean_ctor_set(v_reuseFailAlloc_205_, 6, v_messages_195_);
lean_ctor_set(v_reuseFailAlloc_205_, 7, v_infoState_196_);
lean_ctor_set(v_reuseFailAlloc_205_, 8, v_snapshotTasks_197_);
v___x_203_ = v_reuseFailAlloc_205_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_204_; 
v___x_204_ = lean_st_ref_set(v___x_133_, v___x_203_);
lean_inc(v___x_133_);
lean_inc_ref(v_fileMap_94_);
lean_inc_ref(v_fileName_93_);
v_fileName_145_ = v_fileName_93_;
v_fileMap_146_ = v_fileMap_94_;
v_currRecDepth_147_ = v___x_120_;
v_ref_148_ = v___x_138_;
v_currNamespace_149_ = v___x_96_;
v_openDecls_150_ = v___x_97_;
v_initHeartbeats_151_ = v___x_120_;
v_maxHeartbeats_152_ = v___x_139_;
v_quotContext_153_ = v___x_96_;
v_currMacroScope_154_ = v___x_121_;
v_cancelTk_x3f_155_ = v___x_141_;
v_suppressElabErrors_156_ = v___x_140_;
v_inheritedTraceOptions_157_ = v___x_135_;
v___y_158_ = v___x_133_;
goto v___jp_144_;
}
}
}
else
{
lean_inc(v___x_133_);
lean_inc_ref(v_fileMap_94_);
lean_inc_ref(v_fileName_93_);
v_fileName_145_ = v_fileName_93_;
v_fileMap_146_ = v_fileMap_94_;
v_currRecDepth_147_ = v___x_120_;
v_ref_148_ = v___x_138_;
v_currNamespace_149_ = v___x_96_;
v_openDecls_150_ = v___x_97_;
v_initHeartbeats_151_ = v___x_120_;
v_maxHeartbeats_152_ = v___x_139_;
v_quotContext_153_ = v___x_96_;
v_currMacroScope_154_ = v___x_121_;
v_cancelTk_x3f_155_ = v___x_141_;
v_suppressElabErrors_156_ = v___x_140_;
v_inheritedTraceOptions_157_ = v___x_135_;
v___y_158_ = v___x_133_;
goto v___jp_144_;
}
}
}
}
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_226_; 
v_a_210_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_226_ == 0)
{
v___x_212_ = v___x_85_;
v_isShared_213_ = v_isSharedCheck_226_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_85_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_226_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_214_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__22, &l_Lake_Toml_loadToml___closed__22_once, _init_l_Lake_Toml_loadToml___closed__22);
v___x_215_ = lean_io_error_to_string(v_a_210_);
v___x_216_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
v___x_217_ = l_Lean_MessageData_ofFormat(v___x_216_);
v___x_218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_214_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = 2;
v___x_220_ = l_Lake_mkMessageNoPos(v_ictx_82_, v___x_218_, v___x_219_);
v___x_221_ = l_Lean_MessageLog_empty;
v___x_222_ = l_Lean_MessageLog_add(v___x_220_, v___x_221_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_222_);
v___x_224_ = v___x_212_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml___boxed(lean_object* v_ictx_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lake_Toml_loadToml(v_ictx_227_);
return v_res_229_;
}
}
lean_object* runtime_initialize_Lean_Parser_Types(uint8_t builtin);
lean_object* runtime_initialize_Lake_Toml_Data_Value(uint8_t builtin);
lean_object* runtime_initialize_Lake_Toml_Elab(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Message(uint8_t builtin);
lean_object* runtime_initialize_Std_Do(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_Load(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
