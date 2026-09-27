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
extern lean_object* l_Lean_Options_empty;
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Data_Trie_empty___redArg();
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkEmptyEnvironment(uint32_t);
extern lean_object* l_Lake_Toml_toml;
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_mkParserErrorMessage(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lake_Toml_elabToml(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* l_Lake_mkExceptionMessage(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
static lean_object* l_Lake_Toml_loadToml___closed__21;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Lake_Toml_loadToml___closed__22;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_Toml_loadToml___closed__23;
static const lean_string_object l_Lake_Toml_loadToml___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "failed to initialize TOML environment: "};
static const lean_object* l_Lake_Toml_loadToml___closed__24 = (const lean_object*)&l_Lake_Toml_loadToml___closed__24_value;
static lean_once_cell_t l_Lake_Toml_loadToml___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_loadToml___closed__25;
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
v___x_58_ = l_Lean_Options_empty;
v___x_59_ = ((lean_object*)(l_Lake_Toml_loadToml___closed__18));
v___x_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v___x_58_);
return v___x_60_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__20(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = l_Lean_NameSet_empty;
v___x_62_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__13, &l_Lake_Toml_loadToml___closed__13_once, _init_l_Lake_Toml_loadToml___closed__13);
v___x_63_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
lean_ctor_set(v___x_63_, 2, v___x_61_);
return v___x_63_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__21(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = l_Lean_maxRecDepth;
v___x_65_ = l_Lean_Options_empty;
v___x_66_ = l_Lean_Option_get___at___00Lake_Toml_loadToml_spec__0(v___x_65_, v___x_64_);
return v___x_66_;
}
}
static uint16_t _init_l_Lake_Toml_loadToml___closed__22(void){
_start:
{
uint16_t v___x_67_; uint16_t v___x_68_; uint16_t v___x_69_; 
v___x_67_ = 512;
v___x_68_ = lean_uint16_once(&l_Lake_Toml_loadToml___closed__6, &l_Lake_Toml_loadToml___closed__6_once, _init_l_Lake_Toml_loadToml___closed__6);
v___x_69_ = lean_uint16_land(v___x_68_, v___x_67_);
return v___x_69_;
}
}
static uint8_t _init_l_Lake_Toml_loadToml___closed__23(void){
_start:
{
uint16_t v___x_70_; uint16_t v___x_71_; uint8_t v___x_72_; 
v___x_70_ = 0;
v___x_71_ = lean_uint16_once(&l_Lake_Toml_loadToml___closed__22, &l_Lake_Toml_loadToml___closed__22_once, _init_l_Lake_Toml_loadToml___closed__22);
v___x_72_ = lean_uint16_dec_eq(v___x_71_, v___x_70_);
return v___x_72_;
}
}
static lean_object* _init_l_Lake_Toml_loadToml___closed__25(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = ((lean_object*)(l_Lake_Toml_loadToml___closed__24));
v___x_75_ = l_Lean_stringToMessageData(v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object* v_ictx_76_){
_start:
{
lean_object* v___x_78_; uint32_t v___x_79_; lean_object* v___x_80_; 
v___x_78_ = lean_unsigned_to_nat(0u);
v___x_79_ = 0;
v___x_80_ = l_Lean_mkEmptyEnvironment(v___x_79_);
if (lean_obj_tag(v___x_80_) == 0)
{
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_212_; 
v_a_81_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_212_ == 0)
{
v___x_83_ = v___x_80_;
v_isShared_84_ = v_isSharedCheck_212_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_80_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_212_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_85_; lean_object* v_fn_86_; lean_object* v_inputString_87_; lean_object* v_fileName_88_; lean_object* v_fileMap_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v_errorMsg_97_; 
v___x_85_ = l_Lake_Toml_toml;
v_fn_86_ = lean_ctor_get(v___x_85_, 1);
v_inputString_87_ = lean_ctor_get(v_ictx_76_, 0);
v_fileName_88_ = lean_ctor_get(v_ictx_76_, 1);
v_fileMap_89_ = lean_ctor_get(v_ictx_76_, 2);
v___x_90_ = l_Lean_Options_empty;
v___x_91_ = lean_box(0);
v___x_92_ = lean_box(0);
lean_inc(v_a_81_);
v___x_93_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_93_, 0, v_a_81_);
lean_ctor_set(v___x_93_, 1, v___x_90_);
lean_ctor_set(v___x_93_, 2, v___x_91_);
lean_ctor_set(v___x_93_, 3, v___x_92_);
v___x_94_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__0, &l_Lake_Toml_loadToml___closed__0_once, _init_l_Lake_Toml_loadToml___closed__0);
v___x_95_ = l_Lean_Parser_mkParserState(v_inputString_87_);
lean_inc_ref(v_ictx_76_);
lean_inc_ref(v_fn_86_);
v___x_96_ = l_Lean_Parser_ParserFn_run(v_fn_86_, v_ictx_76_, v___x_93_, v___x_94_, v___x_95_);
v_errorMsg_97_ = lean_ctor_get(v___x_96_, 4);
if (lean_obj_tag(v_errorMsg_97_) == 1)
{
lean_object* v_val_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_103_; 
lean_dec(v_a_81_);
v_val_98_ = lean_ctor_get(v_errorMsg_97_, 0);
lean_inc(v_val_98_);
v___x_99_ = l_Lake_mkParserErrorMessage(v_ictx_76_, v___x_96_, v_val_98_);
lean_dec_ref(v___x_96_);
v___x_100_ = l_Lean_MessageLog_empty;
v___x_101_ = l_Lean_MessageLog_add(v___x_99_, v___x_100_);
if (v_isShared_84_ == 0)
{
lean_ctor_set_tag(v___x_83_, 1);
lean_ctor_set(v___x_83_, 0, v___x_101_);
v___x_103_ = v___x_83_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
else
{
lean_object* v_stxStack_105_; lean_object* v_pos_106_; uint8_t v___x_107_; 
v_stxStack_105_ = lean_ctor_get(v___x_96_, 0);
v_pos_106_ = lean_ctor_get(v___x_96_, 2);
v___x_107_ = l_Lean_Parser_InputContext_atEnd(v_ictx_76_, v_pos_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
lean_dec(v_a_81_);
v___x_108_ = ((lean_object*)(l_Lake_Toml_loadToml___closed__4));
v___x_109_ = l_Lake_mkParserErrorMessage(v_ictx_76_, v___x_96_, v___x_108_);
lean_dec_ref(v___x_96_);
v___x_110_ = l_Lean_MessageLog_empty;
v___x_111_ = l_Lean_MessageLog_add(v___x_109_, v___x_110_);
if (v_isShared_84_ == 0)
{
lean_ctor_set_tag(v___x_83_, 1);
lean_ctor_set(v___x_83_, 0, v___x_111_);
v___x_113_ = v___x_83_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
else
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; uint16_t v___x_120_; uint8_t v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v_fileName_136_; lean_object* v_fileMap_137_; lean_object* v_currNamespace_138_; lean_object* v_openDecls_139_; lean_object* v_initHeartbeats_140_; lean_object* v_maxHeartbeats_141_; lean_object* v_quotContext_142_; lean_object* v_currMacroScope_143_; lean_object* v_cancelTk_x3f_144_; lean_object* v_inheritedTraceOptions_145_; lean_object* v_currRecDepth_146_; lean_object* v_ref_147_; uint8_t v_suppressElabErrors_148_; uint8_t v_isRecordingDeps_149_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___y_183_; uint8_t v___y_205_; uint8_t v___y_206_; lean_object* v_env_207_; uint8_t v___x_208_; uint8_t v___y_210_; uint8_t v___x_211_; 
lean_inc_ref(v_stxStack_105_);
lean_dec_ref(v___x_96_);
lean_del_object(v___x_83_);
v___x_115_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_105_);
lean_dec_ref(v_stxStack_105_);
v___x_116_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__5, &l_Lake_Toml_loadToml___closed__5_once, _init_l_Lake_Toml_loadToml___closed__5);
v___x_117_ = l_Lean_firstFrontendMacroScope;
v___x_118_ = lean_box(0);
v___x_119_ = lean_box(0);
v___x_120_ = lean_uint16_once(&l_Lake_Toml_loadToml___closed__6, &l_Lake_Toml_loadToml___closed__6_once, _init_l_Lake_Toml_loadToml___closed__6);
v___x_121_ = 0;
v___x_122_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__7, &l_Lake_Toml_loadToml___closed__7_once, _init_l_Lake_Toml_loadToml___closed__7);
v___x_123_ = ((lean_object*)(l_Lake_Toml_loadToml___closed__10));
v___x_124_ = ((lean_object*)(l_Lake_Toml_loadToml___closed__11));
v___x_125_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__13, &l_Lake_Toml_loadToml___closed__13_once, _init_l_Lake_Toml_loadToml___closed__13);
v___x_126_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__14, &l_Lake_Toml_loadToml___closed__14_once, _init_l_Lake_Toml_loadToml___closed__14);
v___x_127_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__16, &l_Lake_Toml_loadToml___closed__16_once, _init_l_Lake_Toml_loadToml___closed__16);
v___x_128_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__17, &l_Lake_Toml_loadToml___closed__17_once, _init_l_Lake_Toml_loadToml___closed__17);
v___x_129_ = ((lean_object*)(l_Lake_Toml_loadToml___closed__18));
v___x_130_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__19, &l_Lake_Toml_loadToml___closed__19_once, _init_l_Lake_Toml_loadToml___closed__19);
v___x_131_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__20, &l_Lake_Toml_loadToml___closed__20_once, _init_l_Lake_Toml_loadToml___closed__20);
v___x_132_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_132_, 0, v___x_127_);
lean_ctor_set(v___x_132_, 1, v___x_127_);
lean_ctor_set(v___x_132_, 2, v___x_125_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3, v___x_107_);
v___x_133_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_133_, 0, v_a_81_);
lean_ctor_set(v___x_133_, 1, v___x_122_);
lean_ctor_set(v___x_133_, 2, v___x_123_);
lean_ctor_set(v___x_133_, 3, v___x_124_);
lean_ctor_set(v___x_133_, 4, v___x_126_);
lean_ctor_set(v___x_133_, 5, v___x_128_);
lean_ctor_set(v___x_133_, 6, v___x_130_);
lean_ctor_set(v___x_133_, 7, v___x_131_);
lean_ctor_set(v___x_133_, 8, v___x_132_);
lean_ctor_set(v___x_133_, 9, v___x_129_);
v___x_134_ = lean_st_mk_ref(v___x_133_);
v___x_179_ = l_Lean_inheritedTraceOptions;
v___x_180_ = lean_st_ref_get(v___x_179_);
v___x_181_ = lean_st_ref_get(v___x_134_);
v_env_207_ = lean_ctor_get(v___x_181_, 0);
lean_inc_ref(v_env_207_);
lean_dec(v___x_181_);
v___x_208_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_207_);
lean_dec_ref(v_env_207_);
v___x_211_ = lean_uint8_once(&l_Lake_Toml_loadToml___closed__23, &l_Lake_Toml_loadToml___closed__23_once, _init_l_Lake_Toml_loadToml___closed__23);
if (v___x_211_ == 0)
{
if (v___x_107_ == 0)
{
v___y_210_ = v___x_107_;
goto v___jp_209_;
}
else
{
v___y_205_ = v___x_107_;
v___y_206_ = v___x_208_;
goto v___jp_204_;
}
}
else
{
v___y_210_ = v___x_121_;
goto v___jp_209_;
}
v___jp_135_:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_150_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__21, &l_Lake_Toml_loadToml___closed__21_once, _init_l_Lake_Toml_loadToml___closed__21);
lean_inc(v_cancelTk_x3f_144_);
lean_inc(v_currMacroScope_143_);
lean_inc(v_quotContext_142_);
lean_inc(v_maxHeartbeats_141_);
lean_inc(v_openDecls_139_);
lean_inc(v_currNamespace_138_);
v___x_151_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_151_, 0, v_fileName_136_);
lean_ctor_set(v___x_151_, 1, v_fileMap_137_);
lean_ctor_set(v___x_151_, 2, v___x_90_);
lean_ctor_set(v___x_151_, 3, v___x_150_);
lean_ctor_set(v___x_151_, 4, v_currNamespace_138_);
lean_ctor_set(v___x_151_, 5, v_openDecls_139_);
lean_ctor_set(v___x_151_, 6, v_initHeartbeats_140_);
lean_ctor_set(v___x_151_, 7, v_maxHeartbeats_141_);
lean_ctor_set(v___x_151_, 8, v_quotContext_142_);
lean_ctor_set(v___x_151_, 9, v_currMacroScope_143_);
lean_ctor_set(v___x_151_, 10, v_cancelTk_x3f_144_);
lean_ctor_set(v___x_151_, 11, v_inheritedTraceOptions_145_);
lean_inc(v_ref_147_);
v___x_152_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v_currRecDepth_146_);
lean_ctor_set(v___x_152_, 2, v_ref_147_);
lean_ctor_set_uint16(v___x_152_, sizeof(void*)*3, v___x_120_);
lean_ctor_set_uint8(v___x_152_, sizeof(void*)*3 + 2, v_suppressElabErrors_148_);
lean_ctor_set_uint8(v___x_152_, sizeof(void*)*3 + 3, v_isRecordingDeps_149_);
v___x_153_ = l_Lake_Toml_elabToml(v___x_115_, v___x_152_, v___x_134_);
lean_dec_ref_known(v___x_152_, 3);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_167_; 
lean_dec_ref(v_ictx_76_);
v_a_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_167_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_167_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_167_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v_messages_159_; uint8_t v___x_160_; 
v___x_158_ = lean_st_ref_get(v___x_134_);
lean_dec(v___x_134_);
v_messages_159_ = lean_ctor_get(v___x_158_, 7);
lean_inc_ref(v_messages_159_);
lean_dec(v___x_158_);
v___x_160_ = l_Lean_MessageLog_hasErrors(v_messages_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_162_; 
lean_dec_ref(v_messages_159_);
if (v_isShared_157_ == 0)
{
v___x_162_ = v___x_156_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_154_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
else
{
lean_object* v___x_165_; 
lean_dec(v_a_154_);
if (v_isShared_157_ == 0)
{
lean_ctor_set_tag(v___x_156_, 1);
lean_ctor_set(v___x_156_, 0, v_messages_159_);
v___x_165_ = v___x_156_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_messages_159_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_178_; 
lean_dec(v___x_134_);
v_a_168_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_178_ == 0)
{
v___x_170_ = v___x_153_;
v_isShared_171_ = v_isSharedCheck_178_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_153_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_178_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_172_ = l_Lake_mkExceptionMessage(v_ictx_76_, v_a_168_);
v___x_173_ = l_Lean_MessageLog_empty;
v___x_174_ = l_Lean_MessageLog_add(v___x_172_, v___x_173_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_174_);
v___x_176_ = v___x_170_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
v___jp_182_:
{
lean_object* v___x_184_; lean_object* v_env_185_; lean_object* v_nextMacroScope_186_; lean_object* v_ngen_187_; lean_object* v_auxDeclNGen_188_; lean_object* v_traceState_189_; lean_object* v_recordedDeps_190_; lean_object* v_messages_191_; lean_object* v_infoState_192_; lean_object* v_snapshotTasks_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_202_; 
v___x_184_ = lean_st_ref_take(v___x_134_);
v_env_185_ = lean_ctor_get(v___x_184_, 0);
v_nextMacroScope_186_ = lean_ctor_get(v___x_184_, 1);
v_ngen_187_ = lean_ctor_get(v___x_184_, 2);
v_auxDeclNGen_188_ = lean_ctor_get(v___x_184_, 3);
v_traceState_189_ = lean_ctor_get(v___x_184_, 4);
v_recordedDeps_190_ = lean_ctor_get(v___x_184_, 6);
v_messages_191_ = lean_ctor_get(v___x_184_, 7);
v_infoState_192_ = lean_ctor_get(v___x_184_, 8);
v_snapshotTasks_193_ = lean_ctor_get(v___x_184_, 9);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; 
v_unused_203_ = lean_ctor_get(v___x_184_, 5);
lean_dec(v_unused_203_);
v___x_195_ = v___x_184_;
v_isShared_196_ = v_isSharedCheck_202_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_snapshotTasks_193_);
lean_inc(v_infoState_192_);
lean_inc(v_messages_191_);
lean_inc(v_recordedDeps_190_);
lean_inc(v_traceState_189_);
lean_inc(v_auxDeclNGen_188_);
lean_inc(v_ngen_187_);
lean_inc(v_nextMacroScope_186_);
lean_inc(v_env_185_);
lean_dec(v___x_184_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_202_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_197_ = l_Lean_Kernel_enableDiag(v_env_185_, v___y_183_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 5, v___x_128_);
lean_ctor_set(v___x_195_, 0, v___x_197_);
v___x_199_ = v___x_195_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_nextMacroScope_186_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v_ngen_187_);
lean_ctor_set(v_reuseFailAlloc_201_, 3, v_auxDeclNGen_188_);
lean_ctor_set(v_reuseFailAlloc_201_, 4, v_traceState_189_);
lean_ctor_set(v_reuseFailAlloc_201_, 5, v___x_128_);
lean_ctor_set(v_reuseFailAlloc_201_, 6, v_recordedDeps_190_);
lean_ctor_set(v_reuseFailAlloc_201_, 7, v_messages_191_);
lean_ctor_set(v_reuseFailAlloc_201_, 8, v_infoState_192_);
lean_ctor_set(v_reuseFailAlloc_201_, 9, v_snapshotTasks_193_);
v___x_199_ = v_reuseFailAlloc_201_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_200_; 
v___x_200_ = lean_st_ref_put(v___x_134_, v___x_199_);
lean_inc_ref(v_fileMap_89_);
lean_inc_ref(v_fileName_88_);
v_fileName_136_ = v_fileName_88_;
v_fileMap_137_ = v_fileMap_89_;
v_currNamespace_138_ = v___x_91_;
v_openDecls_139_ = v___x_92_;
v_initHeartbeats_140_ = v___x_78_;
v_maxHeartbeats_141_ = v___x_116_;
v_quotContext_142_ = v___x_91_;
v_currMacroScope_143_ = v___x_117_;
v_cancelTk_x3f_144_ = v___x_118_;
v_inheritedTraceOptions_145_ = v___x_180_;
v_currRecDepth_146_ = v___x_78_;
v_ref_147_ = v___x_119_;
v_suppressElabErrors_148_ = v___x_121_;
v_isRecordingDeps_149_ = v___x_121_;
goto v___jp_135_;
}
}
}
v___jp_204_:
{
if (v___y_206_ == 0)
{
v___y_183_ = v___y_205_;
goto v___jp_182_;
}
else
{
lean_inc_ref(v_fileMap_89_);
lean_inc_ref(v_fileName_88_);
v_fileName_136_ = v_fileName_88_;
v_fileMap_137_ = v_fileMap_89_;
v_currNamespace_138_ = v___x_91_;
v_openDecls_139_ = v___x_92_;
v_initHeartbeats_140_ = v___x_78_;
v_maxHeartbeats_141_ = v___x_116_;
v_quotContext_142_ = v___x_91_;
v_currMacroScope_143_ = v___x_117_;
v_cancelTk_x3f_144_ = v___x_118_;
v_inheritedTraceOptions_145_ = v___x_180_;
v_currRecDepth_146_ = v___x_78_;
v_ref_147_ = v___x_119_;
v_suppressElabErrors_148_ = v___x_121_;
v_isRecordingDeps_149_ = v___x_121_;
goto v___jp_135_;
}
}
v___jp_209_:
{
if (v___x_208_ == 0)
{
v___y_205_ = v___y_210_;
v___y_206_ = v___x_107_;
goto v___jp_204_;
}
else
{
v___y_183_ = v___y_210_;
goto v___jp_182_;
}
}
}
}
}
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_229_; 
v_a_213_ = lean_ctor_get(v___x_80_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_80_);
if (v_isSharedCheck_229_ == 0)
{
v___x_215_ = v___x_80_;
v_isShared_216_ = v_isSharedCheck_229_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_80_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_229_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_217_ = lean_obj_once(&l_Lake_Toml_loadToml___closed__25, &l_Lake_Toml_loadToml___closed__25_once, _init_l_Lake_Toml_loadToml___closed__25);
v___x_218_ = lean_io_error_to_string(v_a_213_);
v___x_219_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
v___x_220_ = l_Lean_MessageData_ofFormat(v___x_219_);
v___x_221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_217_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = 2;
v___x_223_ = l_Lake_mkMessageNoPos(v_ictx_76_, v___x_221_, v___x_222_);
v___x_224_ = l_Lean_MessageLog_empty;
v___x_225_ = l_Lean_MessageLog_add(v___x_223_, v___x_224_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_225_);
v___x_227_ = v___x_215_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml___boxed(lean_object* v_ictx_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lake_Toml_loadToml(v_ictx_230_);
return v_res_232_;
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
