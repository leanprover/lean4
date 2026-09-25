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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Data_Trie_empty___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
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
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lake_Toml_elabToml(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* l_Lake_mkExceptionMessage(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lake_mkMessageNoPos(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0___boxed(lean_object*, lean_object*);
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
static uint16_t l_Lake_Toml_loadToml___closed__6;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_loadToml___closed__7;
static const lean_string_object l_Lake_Toml_loadToml___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_Lake_Toml_loadToml___closed__8 = (const lean_object*)&l_Lake_Toml_loadToml___closed__8_value;
static const lean_ctor_object l_Lake_Toml_loadToml___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Toml_loadToml___closed__8_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_Lake_Toml_loadToml___closed__9 = (const lean_object*)&l_Lake_Toml_loadToml___closed__9_value;
static const lean_ctor_object l_Lake_Toml_loadToml___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Toml_loadToml___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_Toml_loadToml___closed__10 = (const lean_object*)&l_Lake_Toml_loadToml___closed__10_value;
static const lean_ctor_object l_Lake_Toml_loadToml___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_loadToml___closed__11 = (const lean_object*)&l_Lake_Toml_loadToml___closed__11_value;
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
static lean_object* l_Lake_Toml_loadToml___closed__19;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_loadToml___closed__20;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Lake_Toml_loadToml___closed__21;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_Toml_loadToml___closed__22;
static const lean_string_object l_Lake_Toml_loadToml___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "failed to initialize TOML environment: "};
static const lean_object* l_Lake_Toml_loadToml___closed__23 = (const lean_object*)&l_Lake_Toml_loadToml___closed__23_value;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_loadToml___closed__24;
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
lean_inc(v_defValue_4_);
return v_defValue_4_;
}
else
{
lean_object* v_val_7_; 
v_val_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_7_);
lean_dec_ref_known(v___x_6_, 1);
if (lean_obj_tag(v_val_7_) == 3)
{
lean_object* v_v_8_; 
v_v_8_ = lean_ctor_get(v_val_7_, 0);
lean_inc(v_v_8_);
lean_dec_ref_known(v_val_7_, 1);
return v_v_8_;
}
else
{
lean_dec(v_val_7_);
lean_inc(v_defValue_4_);
return v_defValue_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0___boxed(lean_object* v_opts_9_, lean_object* v_opt_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(v_opts_9_, v_opt_10_);
lean_dec_ref(v_opt_10_);
lean_dec_ref(v_opts_9_);
return v_res_11_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__0(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_Data_Trie_empty___redArg();
return v___x_12_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__5(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = l_Lean_Options_empty;
v___x_23_ = l_Lean_Core_getMaxHeartbeats(v___x_22_);
return v___x_23_;
}
}
static uint16_t _init_l_Lake_Toml_loadToml___closed__6(void){
_start:
{
lean_object* v___x_24_; uint16_t v___x_25_; 
v___x_24_ = l_Lean_Options_empty;
v___x_25_ = l_Lean_OptionFlags_ofOptions(v___x_24_);
return v___x_25_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__7(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = l_Lean_firstFrontendMacroScope;
v___x_28_ = lean_nat_add(v___x_27_, v___x_26_);
return v___x_28_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__12(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = lean_unsigned_to_nat(32u);
v___x_40_ = lean_mk_empty_array_with_capacity(v___x_39_);
v___x_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
return v___x_41_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__13(void){
_start:
{
size_t v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_42_ = ((size_t)5ULL);
v___x_43_ = lean_unsigned_to_nat(0u);
v___x_44_ = lean_unsigned_to_nat(32u);
v___x_45_ = lean_mk_empty_array_with_capacity(v___x_44_);
v___x_46_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__12, &l_Lake_Toml_loadToml___closed__12_once, _init_l_Lake_Toml_loadToml___closed__12);
v___x_47_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v___x_45_);
lean_ctor_set(v___x_47_, 2, v___x_43_);
lean_ctor_set(v___x_47_, 3, v___x_43_);
lean_ctor_set_usize(v___x_47_, 4, v___x_42_);
return v___x_47_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__14(void){
_start:
{
lean_object* v___x_48_; uint64_t v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__13, &l_Lake_Toml_loadToml___closed__13_once, _init_l_Lake_Toml_loadToml___closed__13);
v___x_49_ = 0ULL;
v___x_50_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_50_, 0, v___x_48_);
lean_ctor_set_uint64(v___x_50_, sizeof(void*)*1, v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__15(void){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_51_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__16(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__15, &l_Lake_Toml_loadToml___closed__15_once, _init_l_Lake_Toml_loadToml___closed__15);
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__17(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__16, &l_Lake_Toml_loadToml___closed__16_once, _init_l_Lake_Toml_loadToml___closed__16);
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__19(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = l_Lean_NameSet_empty;
v___x_59_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__13, &l_Lake_Toml_loadToml___closed__13_once, _init_l_Lake_Toml_loadToml___closed__13);
v___x_60_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
lean_ctor_set(v___x_60_, 2, v___x_58_);
return v___x_60_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__20(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = l_Lean_maxRecDepth;
v___x_62_ = l_Lean_Options_empty;
v___x_63_ = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(v___x_62_, v___x_61_);
return v___x_63_;
}
}
static uint16_t _init_l_Lake_Toml_loadToml___closed__21(void){
_start:
{
uint16_t v___x_64_; uint16_t v___x_65_; uint16_t v___x_66_; 
v___x_64_ = 512;
v___x_65_ = lean_uint16_once(&l_Lake_Toml_loadToml___closed__6, &l_Lake_Toml_loadToml___closed__6_once, _init_l_Lake_Toml_loadToml___closed__6);
v___x_66_ = lean_uint16_land(v___x_65_, v___x_64_);
return v___x_66_;
}
}
static uint8_t _init_l_Lake_Toml_loadToml___closed__22(void){
_start:
{
uint16_t v___x_67_; uint16_t v___x_68_; uint8_t v___x_69_; 
v___x_67_ = 0;
v___x_68_ = lean_uint16_once(&l_Lake_Toml_loadToml___closed__21, &l_Lake_Toml_loadToml___closed__21_once, _init_l_Lake_Toml_loadToml___closed__21);
v___x_69_ = lean_uint16_dec_eq(v___x_68_, v___x_67_);
return v___x_69_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__24(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = ((lean_object*)(l_Lake_Toml_loadToml___closed__23));
v___x_72_ = l_Lean_stringToMessageData(v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object* v_ictx_73_){
_start:
{
lean_object* v___x_75_; uint32_t v___x_76_; lean_object* v___x_77_; 
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = 0;
v___x_77_ = l_Lean_mkEmptyEnvironment(v___x_76_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_208_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_208_ == 0)
{
v___x_80_ = v___x_77_;
v_isShared_81_ = v_isSharedCheck_208_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_77_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_208_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_82_; lean_object* v_fn_83_; lean_object* v_inputString_84_; lean_object* v_fileName_85_; lean_object* v_fileMap_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v_errorMsg_94_; 
v___x_82_ = l_Lake_Toml_toml;
v_fn_83_ = lean_ctor_get(v___x_82_, 1);
v_inputString_84_ = lean_ctor_get(v_ictx_73_, 0);
v_fileName_85_ = lean_ctor_get(v_ictx_73_, 1);
v_fileMap_86_ = lean_ctor_get(v_ictx_73_, 2);
v___x_87_ = l_Lean_Options_empty;
v___x_88_ = lean_box(0);
v___x_89_ = lean_box(0);
lean_inc(v_a_78_);
v___x_90_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_90_, 0, v_a_78_);
lean_ctor_set(v___x_90_, 1, v___x_87_);
lean_ctor_set(v___x_90_, 2, v___x_88_);
lean_ctor_set(v___x_90_, 3, v___x_89_);
v___x_91_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__0, &l_Lake_Toml_loadToml___closed__0_once, _init_l_Lake_Toml_loadToml___closed__0);
v___x_92_ = l_Lean_Parser_mkParserState(v_inputString_84_);
lean_inc_ref(v_ictx_73_);
lean_inc_ref(v_fn_83_);
v___x_93_ = l_Lean_Parser_ParserFn_run(v_fn_83_, v_ictx_73_, v___x_90_, v___x_91_, v___x_92_);
v_errorMsg_94_ = lean_ctor_get(v___x_93_, 4);
lean_inc(v_errorMsg_94_);
if (lean_obj_tag(v_errorMsg_94_) == 1)
{
lean_object* v_val_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_100_; 
lean_dec(v_a_78_);
v_val_95_ = lean_ctor_get(v_errorMsg_94_, 0);
lean_inc(v_val_95_);
lean_dec_ref_known(v_errorMsg_94_, 1);
v___x_96_ = l_Lake_mkParserErrorMessage(v_ictx_73_, v___x_93_, v_val_95_);
lean_dec_ref(v___x_93_);
v___x_97_ = l_Lean_MessageLog_empty;
v___x_98_ = l_Lean_MessageLog_add(v___x_96_, v___x_97_);
if (v_isShared_81_ == 0)
{
lean_ctor_set_tag(v___x_80_, 1);
lean_ctor_set(v___x_80_, 0, v___x_98_);
v___x_100_ = v___x_80_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v___x_98_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
else
{
lean_object* v_stxStack_102_; lean_object* v_pos_103_; uint8_t v___x_104_; 
lean_dec(v_errorMsg_94_);
v_stxStack_102_ = lean_ctor_get(v___x_93_, 0);
lean_inc_ref(v_stxStack_102_);
v_pos_103_ = lean_ctor_get(v___x_93_, 2);
lean_inc(v_pos_103_);
v___x_104_ = l_Lean_Parser_InputContext_atEnd(v_ictx_73_, v_pos_103_);
lean_dec(v_pos_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
lean_dec_ref(v_stxStack_102_);
lean_dec(v_a_78_);
v___x_105_ = ((lean_object*)(l_Lake_Toml_loadToml___closed__4));
v___x_106_ = l_Lake_mkParserErrorMessage(v_ictx_73_, v___x_93_, v___x_105_);
lean_dec_ref(v___x_93_);
v___x_107_ = l_Lean_MessageLog_empty;
v___x_108_ = l_Lean_MessageLog_add(v___x_106_, v___x_107_);
if (v_isShared_81_ == 0)
{
lean_ctor_set_tag(v___x_80_, 1);
lean_ctor_set(v___x_80_, 0, v___x_108_);
v___x_110_ = v___x_80_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
else
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; uint16_t v___x_117_; uint8_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v_fileName_132_; lean_object* v_fileMap_133_; lean_object* v_currNamespace_134_; lean_object* v_openDecls_135_; lean_object* v_initHeartbeats_136_; lean_object* v_maxHeartbeats_137_; lean_object* v_quotContext_138_; lean_object* v_currMacroScope_139_; lean_object* v_cancelTk_x3f_140_; lean_object* v_inheritedTraceOptions_141_; lean_object* v_currRecDepth_142_; lean_object* v_ref_143_; uint8_t v_suppressElabErrors_144_; uint8_t v_isRecordingDeps_145_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___y_179_; uint8_t v___y_201_; uint8_t v___y_202_; lean_object* v_env_203_; uint8_t v___x_204_; uint8_t v___y_206_; uint8_t v___x_207_; 
lean_dec_ref(v___x_93_);
lean_del_object(v___x_80_);
v___x_112_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_102_);
lean_dec_ref(v_stxStack_102_);
v___x_113_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__5, &l_Lake_Toml_loadToml___closed__5_once, _init_l_Lake_Toml_loadToml___closed__5);
v___x_114_ = l_Lean_firstFrontendMacroScope;
v___x_115_ = lean_box(0);
v___x_116_ = lean_box(0);
v___x_117_ = lean_uint16_once(&l_Lake_Toml_loadToml___closed__6, &l_Lake_Toml_loadToml___closed__6_once, _init_l_Lake_Toml_loadToml___closed__6);
v___x_118_ = 0;
v___x_119_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__7, &l_Lake_Toml_loadToml___closed__7_once, _init_l_Lake_Toml_loadToml___closed__7);
v___x_120_ = ((lean_object*)(l_Lake_Toml_loadToml___closed__10));
v___x_121_ = ((lean_object*)(l_Lake_Toml_loadToml___closed__11));
v___x_122_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__13, &l_Lake_Toml_loadToml___closed__13_once, _init_l_Lake_Toml_loadToml___closed__13);
v___x_123_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__14, &l_Lake_Toml_loadToml___closed__14_once, _init_l_Lake_Toml_loadToml___closed__14);
v___x_124_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__16, &l_Lake_Toml_loadToml___closed__16_once, _init_l_Lake_Toml_loadToml___closed__16);
v___x_125_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__17, &l_Lake_Toml_loadToml___closed__17_once, _init_l_Lake_Toml_loadToml___closed__17);
v___x_126_ = ((lean_object*)(l_Lake_Toml_loadToml___closed__18));
v___x_127_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__19, &l_Lake_Toml_loadToml___closed__19_once, _init_l_Lake_Toml_loadToml___closed__19);
v___x_128_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_128_, 0, v___x_124_);
lean_ctor_set(v___x_128_, 1, v___x_124_);
lean_ctor_set(v___x_128_, 2, v___x_122_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3, v___x_104_);
v___x_129_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_129_, 0, v_a_78_);
lean_ctor_set(v___x_129_, 1, v___x_119_);
lean_ctor_set(v___x_129_, 2, v___x_120_);
lean_ctor_set(v___x_129_, 3, v___x_121_);
lean_ctor_set(v___x_129_, 4, v___x_123_);
lean_ctor_set(v___x_129_, 5, v___x_125_);
lean_ctor_set(v___x_129_, 6, v___x_126_);
lean_ctor_set(v___x_129_, 7, v___x_127_);
lean_ctor_set(v___x_129_, 8, v___x_128_);
lean_ctor_set(v___x_129_, 9, v___x_126_);
v___x_130_ = lean_st_mk_ref(v___x_129_);
v___x_175_ = l_Lean_inheritedTraceOptions;
v___x_176_ = lean_st_ref_get(v___x_175_);
v___x_177_ = lean_st_ref_get(v___x_130_);
v_env_203_ = lean_ctor_get(v___x_177_, 0);
lean_inc_ref(v_env_203_);
lean_dec(v___x_177_);
v___x_204_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_203_);
lean_dec_ref(v_env_203_);
v___x_207_ = lean_uint8_once(&l_Lake_Toml_loadToml___closed__22, &l_Lake_Toml_loadToml___closed__22_once, _init_l_Lake_Toml_loadToml___closed__22);
if (v___x_207_ == 0)
{
if (v___x_104_ == 0)
{
v___y_206_ = v___x_104_;
goto v___jp_205_;
}
else
{
v___y_201_ = v___x_104_;
v___y_202_ = v___x_204_;
goto v___jp_200_;
}
}
else
{
v___y_206_ = v___x_118_;
goto v___jp_205_;
}
v___jp_131_:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_146_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__20, &l_Lake_Toml_loadToml___closed__20_once, _init_l_Lake_Toml_loadToml___closed__20);
lean_inc(v_cancelTk_x3f_140_);
lean_inc(v_currMacroScope_139_);
lean_inc(v_quotContext_138_);
lean_inc(v_maxHeartbeats_137_);
lean_inc(v_openDecls_135_);
lean_inc(v_currNamespace_134_);
v___x_147_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_147_, 0, v_fileName_132_);
lean_ctor_set(v___x_147_, 1, v_fileMap_133_);
lean_ctor_set(v___x_147_, 2, v___x_87_);
lean_ctor_set(v___x_147_, 3, v___x_146_);
lean_ctor_set(v___x_147_, 4, v_currNamespace_134_);
lean_ctor_set(v___x_147_, 5, v_openDecls_135_);
lean_ctor_set(v___x_147_, 6, v_initHeartbeats_136_);
lean_ctor_set(v___x_147_, 7, v_maxHeartbeats_137_);
lean_ctor_set(v___x_147_, 8, v_quotContext_138_);
lean_ctor_set(v___x_147_, 9, v_currMacroScope_139_);
lean_ctor_set(v___x_147_, 10, v_cancelTk_x3f_140_);
lean_ctor_set(v___x_147_, 11, v_inheritedTraceOptions_141_);
lean_inc(v_ref_143_);
v___x_148_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v_currRecDepth_142_);
lean_ctor_set(v___x_148_, 2, v_ref_143_);
lean_ctor_set_uint16(v___x_148_, sizeof(void*)*3, v___x_117_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*3 + 2, v_suppressElabErrors_144_);
lean_ctor_set_uint8(v___x_148_, sizeof(void*)*3 + 3, v_isRecordingDeps_145_);
v___x_149_ = l_Lake_Toml_elabToml(v___x_112_, v___x_148_, v___x_130_);
lean_dec_ref_known(v___x_148_, 3);
if (lean_obj_tag(v___x_149_) == 0)
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_163_; 
lean_dec_ref(v_ictx_73_);
v_a_150_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_163_ == 0)
{
v___x_152_ = v___x_149_;
v_isShared_153_ = v_isSharedCheck_163_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_163_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v_messages_155_; uint8_t v___x_156_; 
v___x_154_ = lean_st_ref_get(v___x_130_);
lean_dec(v___x_130_);
v_messages_155_ = lean_ctor_get(v___x_154_, 7);
lean_inc_ref(v_messages_155_);
lean_dec(v___x_154_);
v___x_156_ = l_Lean_MessageLog_hasErrors(v_messages_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_158_; 
lean_dec_ref(v_messages_155_);
if (v_isShared_153_ == 0)
{
v___x_158_ = v___x_152_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_150_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
else
{
lean_object* v___x_161_; 
lean_dec(v_a_150_);
if (v_isShared_153_ == 0)
{
lean_ctor_set_tag(v___x_152_, 1);
lean_ctor_set(v___x_152_, 0, v_messages_155_);
v___x_161_ = v___x_152_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_messages_155_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
else
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_174_; 
lean_dec(v___x_130_);
v_a_164_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_174_ == 0)
{
v___x_166_ = v___x_149_;
v_isShared_167_ = v_isSharedCheck_174_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_149_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_174_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_168_ = l_Lake_mkExceptionMessage(v_ictx_73_, v_a_164_);
v___x_169_ = l_Lean_MessageLog_empty;
v___x_170_ = l_Lean_MessageLog_add(v___x_168_, v___x_169_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v___x_170_);
v___x_172_ = v___x_166_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
v___jp_178_:
{
lean_object* v___x_180_; lean_object* v_env_181_; lean_object* v_nextMacroScope_182_; lean_object* v_ngen_183_; lean_object* v_auxDeclNGen_184_; lean_object* v_traceState_185_; lean_object* v_recordedDeps_186_; lean_object* v_messages_187_; lean_object* v_infoState_188_; lean_object* v_snapshotTasks_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_198_; 
v___x_180_ = lean_st_ref_take(v___x_130_);
v_env_181_ = lean_ctor_get(v___x_180_, 0);
v_nextMacroScope_182_ = lean_ctor_get(v___x_180_, 1);
v_ngen_183_ = lean_ctor_get(v___x_180_, 2);
v_auxDeclNGen_184_ = lean_ctor_get(v___x_180_, 3);
v_traceState_185_ = lean_ctor_get(v___x_180_, 4);
v_recordedDeps_186_ = lean_ctor_get(v___x_180_, 6);
v_messages_187_ = lean_ctor_get(v___x_180_, 7);
v_infoState_188_ = lean_ctor_get(v___x_180_, 8);
v_snapshotTasks_189_ = lean_ctor_get(v___x_180_, 9);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_198_ == 0)
{
lean_object* v_unused_199_; 
v_unused_199_ = lean_ctor_get(v___x_180_, 5);
lean_dec(v_unused_199_);
v___x_191_ = v___x_180_;
v_isShared_192_ = v_isSharedCheck_198_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_snapshotTasks_189_);
lean_inc(v_infoState_188_);
lean_inc(v_messages_187_);
lean_inc(v_recordedDeps_186_);
lean_inc(v_traceState_185_);
lean_inc(v_auxDeclNGen_184_);
lean_inc(v_ngen_183_);
lean_inc(v_nextMacroScope_182_);
lean_inc(v_env_181_);
lean_dec(v___x_180_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_198_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_193_ = l_Lean_Kernel_enableDiag(v_env_181_, v___y_179_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 5, v___x_125_);
lean_ctor_set(v___x_191_, 0, v___x_193_);
v___x_195_ = v___x_191_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_nextMacroScope_182_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v_ngen_183_);
lean_ctor_set(v_reuseFailAlloc_197_, 3, v_auxDeclNGen_184_);
lean_ctor_set(v_reuseFailAlloc_197_, 4, v_traceState_185_);
lean_ctor_set(v_reuseFailAlloc_197_, 5, v___x_125_);
lean_ctor_set(v_reuseFailAlloc_197_, 6, v_recordedDeps_186_);
lean_ctor_set(v_reuseFailAlloc_197_, 7, v_messages_187_);
lean_ctor_set(v_reuseFailAlloc_197_, 8, v_infoState_188_);
lean_ctor_set(v_reuseFailAlloc_197_, 9, v_snapshotTasks_189_);
v___x_195_ = v_reuseFailAlloc_197_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_196_; 
v___x_196_ = lean_st_ref_put(v___x_130_, v___x_195_);
lean_inc_ref(v_fileMap_86_);
lean_inc_ref(v_fileName_85_);
v_fileName_132_ = v_fileName_85_;
v_fileMap_133_ = v_fileMap_86_;
v_currNamespace_134_ = v___x_88_;
v_openDecls_135_ = v___x_89_;
v_initHeartbeats_136_ = v___x_75_;
v_maxHeartbeats_137_ = v___x_113_;
v_quotContext_138_ = v___x_88_;
v_currMacroScope_139_ = v___x_114_;
v_cancelTk_x3f_140_ = v___x_115_;
v_inheritedTraceOptions_141_ = v___x_176_;
v_currRecDepth_142_ = v___x_75_;
v_ref_143_ = v___x_116_;
v_suppressElabErrors_144_ = v___x_118_;
v_isRecordingDeps_145_ = v___x_118_;
goto v___jp_131_;
}
}
}
v___jp_200_:
{
if (v___y_202_ == 0)
{
v___y_179_ = v___y_201_;
goto v___jp_178_;
}
else
{
lean_inc_ref(v_fileMap_86_);
lean_inc_ref(v_fileName_85_);
v_fileName_132_ = v_fileName_85_;
v_fileMap_133_ = v_fileMap_86_;
v_currNamespace_134_ = v___x_88_;
v_openDecls_135_ = v___x_89_;
v_initHeartbeats_136_ = v___x_75_;
v_maxHeartbeats_137_ = v___x_113_;
v_quotContext_138_ = v___x_88_;
v_currMacroScope_139_ = v___x_114_;
v_cancelTk_x3f_140_ = v___x_115_;
v_inheritedTraceOptions_141_ = v___x_176_;
v_currRecDepth_142_ = v___x_75_;
v_ref_143_ = v___x_116_;
v_suppressElabErrors_144_ = v___x_118_;
v_isRecordingDeps_145_ = v___x_118_;
goto v___jp_131_;
}
}
v___jp_205_:
{
if (v___x_204_ == 0)
{
v___y_201_ = v___y_206_;
v___y_202_ = v___x_104_;
goto v___jp_200_;
}
else
{
v___y_179_ = v___y_206_;
goto v___jp_178_;
}
}
}
}
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_225_; 
v_a_209_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_225_ == 0)
{
v___x_211_ = v___x_77_;
v_isShared_212_ = v_isSharedCheck_225_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_77_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_225_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_213_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__24, &l_Lake_Toml_loadToml___closed__24_once, _init_l_Lake_Toml_loadToml___closed__24);
v___x_214_ = lean_io_error_to_string(v_a_209_);
v___x_215_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
v___x_216_ = l_Lean_MessageData_ofFormat(v___x_215_);
v___x_217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_213_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = 2;
v___x_219_ = l_Lake_mkMessageNoPos(v_ictx_73_, v___x_217_, v___x_218_);
v___x_220_ = l_Lean_MessageLog_empty;
v___x_221_ = l_Lean_MessageLog_add(v___x_219_, v___x_220_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_221_);
v___x_223_ = v___x_211_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml___boxed(lean_object* v_ictx_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lake_Toml_loadToml(v_ictx_226_);
return v_res_228_;
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
