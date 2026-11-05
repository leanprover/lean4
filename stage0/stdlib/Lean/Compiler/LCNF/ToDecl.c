// Lean compiler output
// Module: Lean.Compiler.LCNF.ToDecl
// Imports: public import Lean.Compiler.InitAttr public import Lean.Compiler.LCNF.ToLCNF import Lean.Compiler.Options import Lean.Meta.Transform import Lean.Meta.Match.MatcherInfo import Init.While import Lean.Compiler.ExportAttr
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedBorrowed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
lean_object* l_Lean_Compiler_mkUnsafeRecName(lean_object*);
uint8_t l_Lean_isExport(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Decl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_Compiler_getInlineAttribute_x3f(lean_object*, lean_object*);
lean_object* l_Lean_getExternAttrData_x3f(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_hasInitAttr(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Compiler_isUnsafeRecName_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(uint8_t, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_toDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " Declaration "};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_toDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 321, .m_capacity = 321, .m_length = 320, .m_data = " is marked as `export` but some of its parameters have borrow annotations.\n Consider using `set_option compiler.ignoreBorrowAnnotation true in` to suppress the borrow annotations in its type.\n If the declaration is part of an `export`/`extern` pair make sure to also suppress the annotations at the `extern` declaration."};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__3;
static const lean_ctor_object l_Lean_Compiler_LCNF_toDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__4_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Compiler_LCNF_toDecl___closed__5;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__6;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__7;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__8;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__9;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__10;
static const lean_array_object l_Lean_Compiler_LCNF_toDecl___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__11_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__12;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__13;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__14;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__15;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__16;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__17;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__18;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__19;
static const lean_string_object l_Lean_Compiler_LCNF_toDecl___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declaration `"};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__20 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__20_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__21;
static const lean_string_object l_Lean_Compiler_LCNF_toDecl___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "` does not have a value"};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__22 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__22_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__23;
static const lean_ctor_object l_Lean_Compiler_LCNF_toDecl___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__24 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__24_value;
static const lean_string_object l_Lean_Compiler_LCNF_toDecl___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "` not found"};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__25 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__25_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__26;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__5(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(lean_object* v_declName_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_4_; lean_object* v_env_5_; lean_object* v___x_6_; uint8_t v___x_7_; lean_object* v___x_8_; 
v___x_4_ = lean_st_ref_get(v_a_2_);
v_env_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref_n(v_env_5_, 2);
lean_dec(v___x_4_);
lean_inc(v_declName_1_);
v___x_6_ = l_Lean_Compiler_mkUnsafeRecName(v_declName_1_);
v___x_7_ = 0;
v___x_8_ = l_Lean_Environment_find_x3f(v_env_5_, v___x_6_, v___x_7_);
if (lean_obj_tag(v___x_8_) == 0)
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = l_Lean_Environment_find_x3f(v_env_5_, v_declName_1_, v___x_7_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
else
{
lean_object* v___x_11_; 
lean_dec_ref(v_env_5_);
lean_dec(v_declName_1_);
v___x_11_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_11_, 0, v___x_8_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg___boxed(lean_object* v_declName_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(v_declName_12_, v_a_13_);
lean_dec(v_a_13_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f(lean_object* v_declName_16_, lean_object* v_a_17_, lean_object* v_a_18_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(v_declName_16_, v_a_18_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___boxed(lean_object* v_declName_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f(v_declName_21_, v_a_22_, v_a_23_);
lean_dec(v_a_23_);
lean_dec_ref(v_a_22_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(lean_object* v_declName_26_, lean_object* v_a_27_){
_start:
{
lean_object* v___x_29_; lean_object* v_env_30_; uint8_t v___x_31_; lean_object* v___x_32_; 
v___x_29_ = lean_st_ref_get(v_a_27_);
v_env_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc_ref_n(v_env_30_, 2);
lean_dec(v___x_29_);
v___x_31_ = 0;
lean_inc(v_declName_26_);
v___x_32_ = l_Lean_Environment_find_x3f(v_env_30_, v_declName_26_, v___x_31_);
if (lean_obj_tag(v___x_32_) == 1)
{
lean_object* v_val_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_67_; 
v_val_33_ = lean_ctor_get(v___x_32_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_67_ == 0)
{
v___x_35_ = v___x_32_;
v_isShared_36_ = v_isSharedCheck_67_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_val_33_);
lean_dec(v___x_32_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_67_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
uint8_t v___x_37_; 
v___x_37_ = l_Lean_ConstantInfo_isUnsafe(v_val_33_);
if (v___x_37_ == 0)
{
uint8_t v___x_38_; 
v___x_38_ = 1;
if (lean_obj_tag(v_val_33_) == 3)
{
lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_57_; 
lean_del_object(v___x_35_);
v_isSharedCheck_57_ = !lean_is_exclusive(v_val_33_);
if (v_isSharedCheck_57_ == 0)
{
lean_object* v_unused_58_; 
v_unused_58_ = lean_ctor_get(v_val_33_, 0);
lean_dec(v_unused_58_);
v___x_40_ = v_val_33_;
v_isShared_41_ = v_isSharedCheck_57_;
goto v_resetjp_39_;
}
else
{
lean_dec(v_val_33_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_57_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = l_Lean_Compiler_mkUnsafeRecName(v_declName_26_);
v___x_43_ = l_Lean_Environment_find_x3f(v_env_30_, v___x_42_, v___x_37_);
if (lean_obj_tag(v___x_43_) == 0)
{
lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_44_ = lean_box(v___x_38_);
if (v_isShared_41_ == 0)
{
lean_ctor_set_tag(v___x_40_, 0);
lean_ctor_set(v___x_40_, 0, v___x_44_);
v___x_46_ = v___x_40_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v___x_44_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
else
{
lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_55_; 
lean_del_object(v___x_40_);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_55_ == 0)
{
lean_object* v_unused_56_; 
v_unused_56_ = lean_ctor_get(v___x_43_, 0);
lean_dec(v_unused_56_);
v___x_49_ = v___x_43_;
v_isShared_50_ = v_isSharedCheck_55_;
goto v_resetjp_48_;
}
else
{
lean_dec(v___x_43_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_55_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_51_; lean_object* v___x_53_; 
v___x_51_ = lean_box(v___x_37_);
if (v_isShared_50_ == 0)
{
lean_ctor_set_tag(v___x_49_, 0);
lean_ctor_set(v___x_49_, 0, v___x_51_);
v___x_53_ = v___x_49_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_51_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
}
}
else
{
lean_object* v___x_59_; lean_object* v___x_61_; 
lean_dec(v_val_33_);
lean_dec_ref(v_env_30_);
lean_dec(v_declName_26_);
v___x_59_ = lean_box(v___x_38_);
if (v_isShared_36_ == 0)
{
lean_ctor_set_tag(v___x_35_, 0);
lean_ctor_set(v___x_35_, 0, v___x_59_);
v___x_61_ = v___x_35_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v___x_59_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
else
{
lean_object* v___x_63_; lean_object* v___x_65_; 
lean_dec(v_val_33_);
lean_dec_ref(v_env_30_);
lean_dec(v_declName_26_);
v___x_63_ = lean_box(v___x_31_);
if (v_isShared_36_ == 0)
{
lean_ctor_set_tag(v___x_35_, 0);
lean_ctor_set(v___x_35_, 0, v___x_63_);
v___x_65_ = v___x_35_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_63_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
else
{
uint8_t v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v___x_32_);
lean_dec_ref(v_env_30_);
lean_dec(v_declName_26_);
v___x_68_ = 1;
v___x_69_ = lean_box(v___x_68_);
v___x_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg___boxed(lean_object* v_declName_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(v_declName_71_, v_a_72_);
lean_dec(v_a_72_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe(lean_object* v_declName_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(v_declName_75_, v_a_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe___boxed(lean_object* v_declName_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Compiler_LCNF_declIsNotUnsafe(v_declName_80_, v_a_81_, v_a_82_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
return v_res_84_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(lean_object* v_opts_85_, lean_object* v_opt_86_){
_start:
{
lean_object* v_name_87_; lean_object* v_defValue_88_; lean_object* v_map_89_; lean_object* v___x_90_; 
v_name_87_ = lean_ctor_get(v_opt_86_, 0);
v_defValue_88_ = lean_ctor_get(v_opt_86_, 1);
v_map_89_ = lean_ctor_get(v_opts_85_, 0);
v___x_90_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_89_, v_name_87_);
if (lean_obj_tag(v___x_90_) == 0)
{
uint8_t v___x_91_; 
v___x_91_ = lean_unbox(v_defValue_88_);
return v___x_91_;
}
else
{
lean_object* v_val_92_; 
v_val_92_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_val_92_);
lean_dec_ref_known(v___x_90_, 1);
if (lean_obj_tag(v_val_92_) == 1)
{
uint8_t v_v_93_; 
v_v_93_ = lean_ctor_get_uint8(v_val_92_, 0);
lean_dec_ref_known(v_val_92_, 0);
return v_v_93_;
}
else
{
uint8_t v___x_94_; 
lean_dec(v_val_92_);
v___x_94_ = lean_unbox(v_defValue_88_);
return v___x_94_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0___boxed(lean_object* v_opts_95_, lean_object* v_opt_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(v_opts_95_, v_opt_96_);
lean_dec_ref(v_opt_96_);
lean_dec_ref(v_opts_95_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_99_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__0);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__1);
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
lean_ctor_set(v___x_104_, 2, v___x_103_);
lean_ctor_set(v___x_104_, 3, v___x_103_);
lean_ctor_set(v___x_104_, 4, v___x_102_);
lean_ctor_set(v___x_104_, 5, v___x_102_);
lean_ctor_set(v___x_104_, 6, v___x_102_);
lean_ctor_set(v___x_104_, 7, v___x_102_);
lean_ctor_set(v___x_104_, 8, v___x_102_);
lean_ctor_set(v___x_104_, 9, v___x_102_);
lean_ctor_set(v___x_104_, 10, v___x_102_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(lean_object* v_msg_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_ref_111_; lean_object* v___x_112_; lean_object* v_env_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_ref_111_ = lean_ctor_get(v___y_108_, 2);
v___x_112_ = lean_st_ref_get(v___y_109_);
v_env_113_ = lean_ctor_get(v___x_112_, 0);
lean_inc_ref(v_env_113_);
lean_dec(v___x_112_);
v___x_114_ = lean_st_ref_get(v___y_107_);
v___x_115_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_106_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_138_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_138_ == 0)
{
v___x_118_ = v___x_115_;
v_isShared_119_ = v_isSharedCheck_138_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_138_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v_lctx_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_136_; 
v_lctx_120_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v___x_114_, 1);
lean_dec(v_unused_137_);
v___x_122_ = v___x_114_;
v_isShared_123_ = v_isSharedCheck_136_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_lctx_120_);
lean_dec(v___x_114_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_136_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_124_ = lean_unbox(v_a_116_);
lean_dec(v_a_116_);
v___x_125_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_120_, v___x_124_);
lean_dec_ref(v_lctx_120_);
v___x_126_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_108_);
v___x_127_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__2, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__2_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__2);
v___x_128_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_128_, 0, v_env_113_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
lean_ctor_set(v___x_128_, 2, v___x_125_);
lean_ctor_set(v___x_128_, 3, v___x_126_);
if (v_isShared_123_ == 0)
{
lean_ctor_set_tag(v___x_122_, 3);
lean_ctor_set(v___x_122_, 1, v_msg_105_);
lean_ctor_set(v___x_122_, 0, v___x_128_);
v___x_130_ = v___x_122_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_128_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_msg_105_);
v___x_130_ = v_reuseFailAlloc_135_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
lean_object* v___x_131_; lean_object* v___x_133_; 
lean_inc(v_ref_111_);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v_ref_111_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
if (v_isShared_119_ == 0)
{
lean_ctor_set_tag(v___x_118_, 1);
lean_ctor_set(v___x_118_, 0, v___x_131_);
v___x_133_ = v___x_118_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
lean_dec(v___x_114_);
lean_dec_ref(v_env_113_);
lean_dec_ref(v_msg_105_);
v_a_139_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_115_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_115_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___boxed(lean_object* v_msg_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v_msg_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4(lean_object* v_00_u03b1_154_, lean_object* v_msg_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v_msg_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___boxed(lean_object* v_00_u03b1_162_, lean_object* v_msg_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4(v_00_u03b1_162_, v_msg_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg___lam__0(lean_object* v_k_170_, lean_object* v_b_171_, lean_object* v_c_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v___x_178_; 
lean_inc(v___y_176_);
lean_inc_ref(v___y_175_);
lean_inc(v___y_174_);
lean_inc_ref(v___y_173_);
v___x_178_ = lean_apply_7(v_k_170_, v_b_171_, v_c_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, lean_box(0));
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg___lam__0___boxed(lean_object* v_k_179_, lean_object* v_b_180_, lean_object* v_c_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg___lam__0(v_k_179_, v_b_180_, v_c_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg(lean_object* v_e_188_, lean_object* v_k_189_, uint8_t v_cleanupAnnotations_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v___f_196_; uint8_t v___x_197_; uint8_t v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___f_196_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_196_, 0, v_k_189_);
v___x_197_ = 1;
v___x_198_ = 0;
v___x_199_ = lean_box(0);
v___x_200_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_188_, v___x_197_, v___x_198_, v___x_197_, v___x_198_, v___x_199_, v___f_196_, v_cleanupAnnotations_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
v_a_209_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___x_200_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_200_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_209_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg___boxed(lean_object* v_e_217_, lean_object* v_k_218_, lean_object* v_cleanupAnnotations_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_225_; lean_object* v_res_226_; 
v_cleanupAnnotations_boxed_225_ = lean_unbox(v_cleanupAnnotations_219_);
v_res_226_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg(v_e_217_, v_k_218_, v_cleanupAnnotations_boxed_225_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6(lean_object* v_00_u03b1_227_, lean_object* v_e_228_, lean_object* v_k_229_, uint8_t v_cleanupAnnotations_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg(v_e_228_, v_k_229_, v_cleanupAnnotations_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___boxed(lean_object* v_00_u03b1_237_, lean_object* v_e_238_, lean_object* v_k_239_, lean_object* v_cleanupAnnotations_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_246_; lean_object* v_res_247_; 
v_cleanupAnnotations_boxed_246_ = lean_unbox(v_cleanupAnnotations_240_);
v_res_247_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6(v_00_u03b1_237_, v_e_238_, v_k_239_, v_cleanupAnnotations_boxed_246_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(uint8_t v___x_248_, lean_object* v_a_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_snd_255_; 
v_snd_255_ = lean_ctor_get(v_a_249_, 1);
lean_inc(v_snd_255_);
if (lean_obj_tag(v_snd_255_) == 7)
{
lean_object* v_fst_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_283_; 
v_fst_256_ = lean_ctor_get(v_a_249_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v_a_249_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; 
v_unused_284_ = lean_ctor_get(v_a_249_, 1);
lean_dec(v_unused_284_);
v___x_258_ = v_a_249_;
v_isShared_259_ = v_isSharedCheck_283_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_fst_256_);
lean_dec(v_a_249_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_283_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v_binderName_260_; lean_object* v_binderType_261_; lean_object* v_body_262_; uint8_t v___y_264_; 
v_binderName_260_ = lean_ctor_get(v_snd_255_, 0);
lean_inc(v_binderName_260_);
v_binderType_261_ = lean_ctor_get(v_snd_255_, 1);
lean_inc_ref(v_binderType_261_);
v_body_262_ = lean_ctor_get(v_snd_255_, 2);
lean_inc_ref(v_body_262_);
lean_dec_ref_known(v_snd_255_, 3);
if (v___x_248_ == 0)
{
uint8_t v___x_281_; 
v___x_281_ = l_Lean_isMarkedBorrowed(v_binderType_261_);
v___y_264_ = v___x_281_;
goto v___jp_263_;
}
else
{
uint8_t v___x_282_; 
v___x_282_ = 0;
v___y_264_ = v___x_282_;
goto v___jp_263_;
}
v___jp_263_:
{
uint8_t v___x_265_; lean_object* v___x_266_; 
v___x_265_ = 0;
v___x_266_ = l_Lean_Compiler_LCNF_mkParam(v___x_265_, v_binderName_260_, v_binderType_261_, v___y_264_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_268_; lean_object* v___x_270_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_267_);
lean_dec_ref_known(v___x_266_, 1);
v___x_268_ = lean_array_push(v_fst_256_, v_a_267_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 1, v_body_262_);
lean_ctor_set(v___x_258_, 0, v___x_268_);
v___x_270_ = v___x_258_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_268_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_body_262_);
v___x_270_ = v_reuseFailAlloc_272_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
v_a_249_ = v___x_270_;
goto _start;
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
lean_dec_ref(v_body_262_);
lean_del_object(v___x_258_);
lean_dec(v_fst_256_);
v_a_273_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_266_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_266_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
}
else
{
lean_object* v_fst_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_293_; 
v_fst_285_ = lean_ctor_get(v_a_249_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v_a_249_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; 
v_unused_294_ = lean_ctor_get(v_a_249_, 1);
lean_dec(v_unused_294_);
v___x_287_ = v_a_249_;
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_fst_285_);
lean_dec(v_a_249_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_fst_285_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_snd_255_);
v___x_290_ = v_reuseFailAlloc_292_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_291_; 
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
return v___x_291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg___boxed(lean_object* v___x_295_, lean_object* v_a_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
uint8_t v___x_14044__boxed_302_; lean_object* v_res_303_; 
v___x_14044__boxed_302_ = lean_unbox(v___x_295_);
v_res_303_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_14044__boxed_302_, v_a_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0(lean_object* v_expr_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_312_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0));
v___x_313_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_309_);
v___x_314_ = l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
v___x_315_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(v___x_313_, v___x_314_);
lean_dec_ref(v___x_313_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_312_);
lean_ctor_set(v___x_316_, 1, v_expr_306_);
v___x_317_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_315_, v___x_316_, v___y_307_, v___y_308_, v___y_309_, v___y_310_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_326_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_326_ == 0)
{
v___x_320_ = v___x_317_;
v_isShared_321_ = v_isSharedCheck_326_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_326_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v_fst_322_; lean_object* v___x_324_; 
v_fst_322_ = lean_ctor_get(v_a_318_, 0);
lean_inc(v_fst_322_);
lean_dec(v_a_318_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v_fst_322_);
v___x_324_ = v___x_320_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_fst_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
v_a_327_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_317_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_317_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0___boxed(lean_object* v_expr_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_Compiler_LCNF_toDecl___lam__0(v_expr_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1(uint8_t v___x_342_, uint8_t v___x_343_, lean_object* v_xs_344_, lean_object* v_body_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_Meta_etaExpand(v_body_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; uint8_t v___x_353_; lean_object* v___x_354_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref_known(v___x_351_, 1);
v___x_353_ = 1;
v___x_354_ = l_Lean_Meta_mkLambdaFVars(v_xs_344_, v_a_352_, v___x_342_, v___x_343_, v___x_342_, v___x_343_, v___x_353_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
return v___x_354_;
}
else
{
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1___boxed(lean_object* v___x_355_, lean_object* v___x_356_, lean_object* v_xs_357_, lean_object* v_body_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
uint8_t v___x_14202__boxed_364_; uint8_t v___x_14203__boxed_365_; lean_object* v_res_366_; 
v___x_14202__boxed_364_ = lean_unbox(v___x_355_);
v___x_14203__boxed_365_ = lean_unbox(v___x_356_);
v_res_366_ = l_Lean_Compiler_LCNF_toDecl___lam__1(v___x_14202__boxed_364_, v___x_14203__boxed_365_, v_xs_357_, v_body_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec_ref(v_xs_357_);
return v_res_366_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(lean_object* v_as_367_, size_t v_i_368_, size_t v_stop_369_){
_start:
{
uint8_t v___x_370_; 
v___x_370_ = lean_usize_dec_eq(v_i_368_, v_stop_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; uint8_t v_borrow_372_; 
v___x_371_ = lean_array_uget_borrowed(v_as_367_, v_i_368_);
v_borrow_372_ = lean_ctor_get_uint8(v___x_371_, sizeof(void*)*3);
if (v_borrow_372_ == 0)
{
size_t v___x_373_; size_t v___x_374_; 
v___x_373_ = ((size_t)1ULL);
v___x_374_ = lean_usize_add(v_i_368_, v___x_373_);
v_i_368_ = v___x_374_;
goto _start;
}
else
{
return v_borrow_372_;
}
}
else
{
uint8_t v___x_376_; 
v___x_376_ = 0;
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3___boxed(lean_object* v_as_377_, lean_object* v_i_378_, lean_object* v_stop_379_){
_start:
{
size_t v_i_boxed_380_; size_t v_stop_boxed_381_; uint8_t v_res_382_; lean_object* v_r_383_; 
v_i_boxed_380_ = lean_unbox_usize(v_i_378_);
lean_dec(v_i_378_);
v_stop_boxed_381_ = lean_unbox_usize(v_stop_379_);
lean_dec(v_stop_379_);
v_res_382_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(v_as_377_, v_i_boxed_380_, v_stop_boxed_381_);
lean_dec_ref(v_as_377_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__0);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2___redArg(){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2___redArg___closed__0);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2___redArg___boxed(lean_object* v___dummy_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2___redArg();
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(uint8_t v___x_390_, size_t v_sz_391_, size_t v_i_392_, lean_object* v_bs_393_, lean_object* v___y_394_){
_start:
{
uint8_t v___x_396_; 
v___x_396_ = lean_usize_dec_lt(v_i_392_, v_sz_391_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; 
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v_bs_393_);
return v___x_397_;
}
else
{
lean_object* v_v_398_; lean_object* v___x_399_; lean_object* v_bs_x27_400_; uint8_t v___x_401_; lean_object* v___x_402_; 
v_v_398_ = lean_array_uget(v_bs_393_, v_i_392_);
v___x_399_ = lean_unsigned_to_nat(0u);
v_bs_x27_400_ = lean_array_uset(v_bs_393_, v_i_392_, v___x_399_);
v___x_401_ = 0;
v___x_402_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v___x_401_, v_v_398_, v___x_390_, v___y_394_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; size_t v___x_404_; size_t v___x_405_; lean_object* v___x_406_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_a_403_);
lean_dec_ref_known(v___x_402_, 1);
v___x_404_ = ((size_t)1ULL);
v___x_405_ = lean_usize_add(v_i_392_, v___x_404_);
v___x_406_ = lean_array_uset(v_bs_x27_400_, v_i_392_, v_a_403_);
v_i_392_ = v___x_405_;
v_bs_393_ = v___x_406_;
goto _start;
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_dec_ref(v_bs_x27_400_);
v_a_408_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_402_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_402_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___boxed(lean_object* v___x_416_, lean_object* v_sz_417_, lean_object* v_i_418_, lean_object* v_bs_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
uint8_t v___x_14253__boxed_422_; size_t v_sz_boxed_423_; size_t v_i_boxed_424_; lean_object* v_res_425_; 
v___x_14253__boxed_422_ = lean_unbox(v___x_416_);
v_sz_boxed_423_ = lean_unbox_usize(v_sz_417_);
lean_dec(v_sz_417_);
v_i_boxed_424_ = lean_unbox_usize(v_i_418_);
lean_dec(v_i_418_);
v_res_425_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v___x_14253__boxed_422_, v_sz_boxed_423_, v_i_boxed_424_, v_bs_419_, v___y_420_);
lean_dec(v___y_420_);
return v_res_425_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__1(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__0));
v___x_428_ = l_Lean_stringToMessageData(v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__3(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__2));
v___x_431_ = l_Lean_stringToMessageData(v___x_430_);
return v___x_431_;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_toDecl___closed__5(void){
_start:
{
lean_object* v___x_438_; uint64_t v___x_439_; 
v___x_438_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__4));
v___x_439_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_438_);
return v___x_439_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__6(void){
_start:
{
uint64_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_uint64_once(&l_Lean_Compiler_LCNF_toDecl___closed__5, &l_Lean_Compiler_LCNF_toDecl___closed__5_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__5);
v___x_441_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__4));
v___x_442_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set_uint64(v___x_442_, sizeof(void*)*1, v___x_440_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__7(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__0);
v___x_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__8(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = lean_unsigned_to_nat(32u);
v___x_446_ = lean_mk_empty_array_with_capacity(v___x_445_);
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__9(void){
_start:
{
size_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_448_ = ((size_t)5ULL);
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = lean_unsigned_to_nat(32u);
v___x_451_ = lean_mk_empty_array_with_capacity(v___x_450_);
v___x_452_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__8, &l_Lean_Compiler_LCNF_toDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__8);
v___x_453_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_451_);
lean_ctor_set(v___x_453_, 2, v___x_449_);
lean_ctor_set(v___x_453_, 3, v___x_449_);
lean_ctor_set_usize(v___x_453_, 4, v___x_448_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__10(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_454_ = lean_box(1);
v___x_455_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__9, &l_Lean_Compiler_LCNF_toDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__9);
v___x_456_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__7, &l_Lean_Compiler_LCNF_toDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__7);
v___x_457_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___x_455_);
lean_ctor_set(v___x_457_, 2, v___x_454_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__12(void){
_start:
{
uint8_t v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_460_ = 1;
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_box(0);
v___x_463_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__11));
v___x_464_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__10, &l_Lean_Compiler_LCNF_toDecl___closed__10_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__10);
v___x_465_ = lean_box(1);
v___x_466_ = 0;
v___x_467_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__6, &l_Lean_Compiler_LCNF_toDecl___closed__6_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__6);
v___x_468_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v___x_465_);
lean_ctor_set(v___x_468_, 2, v___x_464_);
lean_ctor_set(v___x_468_, 3, v___x_463_);
lean_ctor_set(v___x_468_, 4, v___x_462_);
lean_ctor_set(v___x_468_, 5, v___x_461_);
lean_ctor_set(v___x_468_, 6, v___x_462_);
lean_ctor_set_uint8(v___x_468_, sizeof(void*)*7, v___x_466_);
lean_ctor_set_uint8(v___x_468_, sizeof(void*)*7 + 1, v___x_466_);
lean_ctor_set_uint8(v___x_468_, sizeof(void*)*7 + 2, v___x_466_);
lean_ctor_set_uint8(v___x_468_, sizeof(void*)*7 + 3, v___x_460_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__13(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__7, &l_Lean_Compiler_LCNF_toDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__7);
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
lean_ctor_set(v___x_471_, 2, v___x_470_);
lean_ctor_set(v___x_471_, 3, v___x_470_);
lean_ctor_set(v___x_471_, 4, v___x_469_);
lean_ctor_set(v___x_471_, 5, v___x_469_);
lean_ctor_set(v___x_471_, 6, v___x_469_);
lean_ctor_set(v___x_471_, 7, v___x_469_);
lean_ctor_set(v___x_471_, 8, v___x_469_);
lean_ctor_set(v___x_471_, 9, v___x_469_);
lean_ctor_set(v___x_471_, 10, v___x_469_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__14(void){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2___redArg();
return v___x_472_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__15(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__7, &l_Lean_Compiler_LCNF_toDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__7);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__16(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_475_ = lean_unsigned_to_nat(0u);
v___x_476_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__7, &l_Lean_Compiler_LCNF_toDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__7);
v___x_477_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
lean_ctor_set(v___x_477_, 2, v___x_475_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__17(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_478_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__16, &l_Lean_Compiler_LCNF_toDecl___closed__16_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__16);
v___x_479_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__15, &l_Lean_Compiler_LCNF_toDecl___closed__15_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__15);
v___x_480_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__7, &l_Lean_Compiler_LCNF_toDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__7);
v___x_481_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__14, &l_Lean_Compiler_LCNF_toDecl___closed__14_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__14);
v___x_482_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v___x_480_);
lean_ctor_set(v___x_482_, 2, v___x_479_);
lean_ctor_set(v___x_482_, 3, v___x_480_);
lean_ctor_set(v___x_482_, 4, v___x_480_);
lean_ctor_set(v___x_482_, 5, v___x_480_);
lean_ctor_set(v___x_482_, 6, v___x_480_);
lean_ctor_set(v___x_482_, 7, v___x_478_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__18(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__7, &l_Lean_Compiler_LCNF_toDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__7);
v___x_484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v___x_483_);
lean_ctor_set(v___x_484_, 2, v___x_483_);
lean_ctor_set(v___x_484_, 3, v___x_483_);
lean_ctor_set(v___x_484_, 4, v___x_483_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__19(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_485_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__18, &l_Lean_Compiler_LCNF_toDecl___closed__18_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__18);
v___x_486_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__9, &l_Lean_Compiler_LCNF_toDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__9);
v___x_487_ = lean_box(1);
v___x_488_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__17, &l_Lean_Compiler_LCNF_toDecl___closed__17_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__17);
v___x_489_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__13, &l_Lean_Compiler_LCNF_toDecl___closed__13_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__13);
v___x_490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v___x_488_);
lean_ctor_set(v___x_490_, 2, v___x_487_);
lean_ctor_set(v___x_490_, 3, v___x_486_);
lean_ctor_set(v___x_490_, 4, v___x_485_);
return v___x_490_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__21(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__20));
v___x_493_ = l_Lean_stringToMessageData(v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__23(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__22));
v___x_496_ = l_Lean_stringToMessageData(v___x_495_);
return v___x_496_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__26(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__25));
v___x_501_ = l_Lean_stringToMessageData(v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object* v_declName_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v_decl_511_; lean_object* v_name_512_; lean_object* v_params_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_543_; uint8_t v___y_544_; lean_object* v___y_545_; lean_object* v_decl_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; uint8_t v___y_598_; lean_object* v___y_599_; uint8_t v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___x_613_; lean_object* v___y_615_; lean_object* v___x_811_; 
v___x_613_ = lean_box(1);
v___x_811_ = l_Lean_Compiler_isUnsafeRecName_x3f(v_declName_502_);
if (lean_obj_tag(v___x_811_) == 1)
{
lean_object* v_val_812_; 
lean_dec(v_declName_502_);
v_val_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_val_812_);
lean_dec_ref_known(v___x_811_, 1);
v___y_615_ = v_val_812_;
goto v___jp_614_;
}
else
{
lean_dec(v___x_811_);
v___y_615_ = v_declName_502_;
goto v___jp_614_;
}
v___jp_508_:
{
uint8_t v___x_518_; 
lean_inc(v_name_512_);
v___x_518_ = l_Lean_isExport(v___y_510_, v_name_512_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; 
lean_dec_ref(v_params_513_);
lean_dec(v_name_512_);
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v_decl_511_);
return v___x_519_;
}
else
{
lean_object* v___x_520_; uint8_t v___x_521_; 
v___x_520_ = lean_array_get_size(v_params_513_);
v___x_521_ = lean_nat_dec_lt(v___y_509_, v___x_520_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
lean_dec_ref(v_params_513_);
lean_dec(v_name_512_);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v_decl_511_);
return v___x_522_;
}
else
{
if (v___x_521_ == 0)
{
lean_object* v___x_523_; 
lean_dec_ref(v_params_513_);
lean_dec(v_name_512_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v_decl_511_);
return v___x_523_;
}
else
{
size_t v___x_524_; size_t v___x_525_; uint8_t v___x_526_; 
v___x_524_ = ((size_t)0ULL);
v___x_525_ = lean_usize_of_nat(v___x_520_);
v___x_526_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(v_params_513_, v___x_524_, v___x_525_);
lean_dec_ref(v_params_513_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; 
lean_dec(v_name_512_);
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v_decl_511_);
return v___x_527_;
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec_ref(v_decl_511_);
v___x_528_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__1, &l_Lean_Compiler_LCNF_toDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__1);
v___x_529_ = l_Lean_MessageData_ofName(v_name_512_);
v___x_530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__3, &l_Lean_Compiler_LCNF_toDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__3);
v___x_532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___x_532_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
v_a_534_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_533_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_533_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
}
}
v___jp_542_:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_Compiler_LCNF_Decl_etaExpand(v_decl_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_a_552_);
lean_dec_ref_known(v___x_551_, 1);
v___x_553_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_549_);
v___x_554_ = l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
v___x_555_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(v___x_553_, v___x_554_);
lean_dec_ref(v___x_553_);
if (v___x_555_ == 0)
{
lean_object* v_toSignature_556_; lean_object* v_name_557_; lean_object* v_params_558_; 
v_toSignature_556_ = lean_ctor_get(v_a_552_, 0);
v_name_557_ = lean_ctor_get(v_toSignature_556_, 0);
lean_inc(v_name_557_);
v_params_558_ = lean_ctor_get(v_toSignature_556_, 3);
lean_inc_ref(v_params_558_);
v___y_509_ = v___y_543_;
v___y_510_ = v___y_545_;
v_decl_511_ = v_a_552_;
v_name_512_ = v_name_557_;
v_params_513_ = v_params_558_;
v___y_514_ = v___y_547_;
v___y_515_ = v___y_548_;
v___y_516_ = v___y_549_;
v___y_517_ = v___y_550_;
goto v___jp_508_;
}
else
{
lean_object* v_toSignature_559_; lean_object* v_value_560_; uint8_t v_recursive_561_; lean_object* v_inlineAttr_x3f_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_593_; 
v_toSignature_559_ = lean_ctor_get(v_a_552_, 0);
v_value_560_ = lean_ctor_get(v_a_552_, 1);
v_recursive_561_ = lean_ctor_get_uint8(v_a_552_, sizeof(void*)*3);
v_inlineAttr_x3f_562_ = lean_ctor_get(v_a_552_, 2);
v_isSharedCheck_593_ = !lean_is_exclusive(v_a_552_);
if (v_isSharedCheck_593_ == 0)
{
v___x_564_ = v_a_552_;
v_isShared_565_ = v_isSharedCheck_593_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_inlineAttr_x3f_562_);
lean_inc(v_value_560_);
lean_inc(v_toSignature_559_);
lean_dec(v_a_552_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_593_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v_name_566_; lean_object* v_levelParams_567_; lean_object* v_type_568_; lean_object* v_params_569_; uint8_t v_safe_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_592_; 
v_name_566_ = lean_ctor_get(v_toSignature_559_, 0);
v_levelParams_567_ = lean_ctor_get(v_toSignature_559_, 1);
v_type_568_ = lean_ctor_get(v_toSignature_559_, 2);
v_params_569_ = lean_ctor_get(v_toSignature_559_, 3);
v_safe_570_ = lean_ctor_get_uint8(v_toSignature_559_, sizeof(void*)*4);
v_isSharedCheck_592_ = !lean_is_exclusive(v_toSignature_559_);
if (v_isSharedCheck_592_ == 0)
{
v___x_572_ = v_toSignature_559_;
v_isShared_573_ = v_isSharedCheck_592_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_params_569_);
lean_inc(v_type_568_);
lean_inc(v_levelParams_567_);
lean_inc(v_name_566_);
lean_dec(v_toSignature_559_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_592_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
size_t v_sz_574_; size_t v___x_575_; lean_object* v___x_576_; 
v_sz_574_ = lean_array_size(v_params_569_);
v___x_575_ = ((size_t)0ULL);
v___x_576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v___y_544_, v_sz_574_, v___x_575_, v_params_569_, v___y_548_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_579_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc_n(v_a_577_, 2);
lean_dec_ref_known(v___x_576_, 1);
lean_inc(v_name_566_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 3, v_a_577_);
v___x_579_ = v___x_572_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_name_566_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_levelParams_567_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v_type_568_);
lean_ctor_set(v_reuseFailAlloc_583_, 3, v_a_577_);
lean_ctor_set_uint8(v_reuseFailAlloc_583_, sizeof(void*)*4, v_safe_570_);
v___x_579_ = v_reuseFailAlloc_583_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_581_; 
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_579_);
v___x_581_ = v___x_564_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_value_560_);
lean_ctor_set(v_reuseFailAlloc_582_, 2, v_inlineAttr_x3f_562_);
lean_ctor_set_uint8(v_reuseFailAlloc_582_, sizeof(void*)*3, v_recursive_561_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
v___y_509_ = v___y_543_;
v___y_510_ = v___y_545_;
v_decl_511_ = v___x_581_;
v_name_512_ = v_name_566_;
v_params_513_ = v_a_577_;
v___y_514_ = v___y_547_;
v___y_515_ = v___y_548_;
v___y_516_ = v___y_549_;
v___y_517_ = v___y_550_;
goto v___jp_508_;
}
}
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
lean_del_object(v___x_572_);
lean_dec_ref(v_type_568_);
lean_dec(v_levelParams_567_);
lean_dec(v_name_566_);
lean_del_object(v___x_564_);
lean_dec(v_inlineAttr_x3f_562_);
lean_dec_ref(v_value_560_);
lean_dec_ref(v___y_545_);
v_a_584_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_576_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_576_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_545_);
return v___x_551_;
}
}
v___jp_594_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_608_ = l_Lean_ConstantInfo_levelParams(v___y_599_);
lean_dec_ref(v___y_599_);
v___x_609_ = lean_mk_empty_array_with_capacity(v___y_596_);
v___x_610_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_610_, 0, v___y_595_);
lean_ctor_set(v___x_610_, 1, v___x_608_);
lean_ctor_set(v___x_610_, 2, v___y_597_);
lean_ctor_set(v___x_610_, 3, v___x_609_);
lean_ctor_set_uint8(v___x_610_, sizeof(void*)*4, v___y_600_);
v___x_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_611_, 0, v___y_601_);
v___x_612_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
lean_ctor_set(v___x_612_, 2, v___y_602_);
lean_ctor_set_uint8(v___x_612_, sizeof(void*)*3, v___y_598_);
v___y_543_ = v___y_596_;
v___y_544_ = v___y_598_;
v___y_545_ = v___y_603_;
v_decl_546_ = v___x_612_;
v___y_547_ = v___y_604_;
v___y_548_ = v___y_605_;
v___y_549_ = v___y_606_;
v___y_550_ = v___y_607_;
goto v___jp_542_;
}
v___jp_614_:
{
lean_object* v___x_616_; lean_object* v_a_617_; 
lean_inc(v___y_615_);
v___x_616_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(v___y_615_, v_a_506_);
v_a_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_a_617_);
lean_dec_ref(v___x_616_);
if (lean_obj_tag(v_a_617_) == 1)
{
lean_object* v_val_618_; lean_object* v___x_619_; lean_object* v_a_620_; lean_object* v___x_621_; lean_object* v_env_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_val_618_ = lean_ctor_get(v_a_617_, 0);
lean_inc(v_val_618_);
lean_dec_ref_known(v_a_617_, 1);
lean_inc_n(v___y_615_, 3);
v___x_619_ = l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(v___y_615_, v_a_506_);
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_a_620_);
lean_dec_ref(v___x_619_);
v___x_621_ = lean_st_ref_get(v_a_506_);
v_env_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc_ref_n(v_env_622_, 3);
lean_dec(v___x_621_);
v___x_623_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_622_, v___y_615_);
v___x_624_ = l_Lean_getExternAttrData_x3f(v_env_622_, v___y_615_);
if (lean_obj_tag(v___x_624_) == 1)
{
lean_object* v_val_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_669_; 
lean_dec_ref(v_env_622_);
v_val_625_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_669_ == 0)
{
v___x_627_ = v___x_624_;
v_isShared_628_ = v_isSharedCheck_669_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_val_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_669_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; uint8_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_629_ = l_Lean_ConstantInfo_type(v_val_618_);
v___x_630_ = 0;
v___x_631_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__12, &l_Lean_Compiler_LCNF_toDecl___closed__12_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__12);
v___x_632_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__19, &l_Lean_Compiler_LCNF_toDecl___closed__19_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__19);
v___x_633_ = lean_st_mk_ref(v___x_632_);
v___x_634_ = l_Lean_Compiler_LCNF_toLCNFType(v___x_629_, v___x_631_, v___x_633_, v_a_505_, v_a_506_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc_n(v_a_635_, 2);
lean_dec_ref_known(v___x_634_, 1);
v___x_636_ = lean_st_ref_get(v___x_633_);
lean_dec(v___x_633_);
lean_dec(v___x_636_);
v___x_637_ = l_Lean_Compiler_LCNF_toDecl___lam__0(v_a_635_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_652_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_652_ == 0)
{
v___x_640_ = v___x_637_;
v_isShared_641_ = v_isSharedCheck_652_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_637_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_652_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; lean_object* v___x_646_; 
v___x_642_ = l_Lean_ConstantInfo_levelParams(v_val_618_);
lean_dec(v_val_618_);
v___x_643_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_643_, 0, v___y_615_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
lean_ctor_set(v___x_643_, 2, v_a_635_);
lean_ctor_set(v___x_643_, 3, v_a_638_);
v___x_644_ = lean_unbox(v_a_620_);
lean_dec(v_a_620_);
lean_ctor_set_uint8(v___x_643_, sizeof(void*)*4, v___x_644_);
if (v_isShared_628_ == 0)
{
v___x_646_ = v___x_627_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_val_625_);
v___x_646_ = v_reuseFailAlloc_651_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_647_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_647_, 0, v___x_643_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
lean_ctor_set(v___x_647_, 2, v___x_623_);
lean_ctor_set_uint8(v___x_647_, sizeof(void*)*3, v___x_630_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_647_);
v___x_649_ = v___x_640_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_dec(v_a_635_);
lean_del_object(v___x_627_);
lean_dec(v_val_625_);
lean_dec(v___x_623_);
lean_dec(v_a_620_);
lean_dec(v_val_618_);
lean_dec(v___y_615_);
v_a_653_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_637_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_637_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec(v___x_633_);
lean_del_object(v___x_627_);
lean_dec(v_val_625_);
lean_dec(v___x_623_);
lean_dec(v_a_620_);
lean_dec(v_val_618_);
lean_dec(v___y_615_);
v_a_661_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_634_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_634_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
else
{
uint8_t v___x_670_; uint8_t v___x_671_; 
lean_dec(v___x_624_);
lean_inc(v___y_615_);
lean_inc_ref(v_env_622_);
v___x_670_ = l_Lean_hasInitAttr(v_env_622_, v___y_615_);
v___x_671_ = 1;
if (v___x_670_ == 0)
{
lean_object* v___x_672_; 
lean_inc(v_val_618_);
v___x_672_ = l_Lean_ConstantInfo_value_x3f(v_val_618_, v___x_671_);
if (lean_obj_tag(v___x_672_) == 1)
{
lean_object* v_val_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___f_676_; lean_object* v___x_677_; uint8_t v___x_678_; uint8_t v___x_679_; uint8_t v___x_680_; lean_object* v___x_681_; uint64_t v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v_val_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_val_673_);
lean_dec_ref_known(v___x_672_, 1);
v___x_674_ = lean_box(v___x_670_);
v___x_675_ = lean_box(v___x_671_);
v___f_676_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toDecl___lam__1___boxed), 9, 2);
lean_closure_set(v___f_676_, 0, v___x_674_);
lean_closure_set(v___f_676_, 1, v___x_675_);
v___x_677_ = l_Lean_ConstantInfo_type(v_val_618_);
v___x_678_ = 1;
v___x_679_ = 0;
v___x_680_ = 2;
v___x_681_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_681_, 0, v___x_670_);
lean_ctor_set_uint8(v___x_681_, 1, v___x_670_);
lean_ctor_set_uint8(v___x_681_, 2, v___x_670_);
lean_ctor_set_uint8(v___x_681_, 3, v___x_670_);
lean_ctor_set_uint8(v___x_681_, 4, v___x_670_);
lean_ctor_set_uint8(v___x_681_, 5, v___x_671_);
lean_ctor_set_uint8(v___x_681_, 6, v___x_671_);
lean_ctor_set_uint8(v___x_681_, 7, v___x_670_);
lean_ctor_set_uint8(v___x_681_, 8, v___x_671_);
lean_ctor_set_uint8(v___x_681_, 9, v___x_678_);
lean_ctor_set_uint8(v___x_681_, 10, v___x_679_);
lean_ctor_set_uint8(v___x_681_, 11, v___x_671_);
lean_ctor_set_uint8(v___x_681_, 12, v___x_671_);
lean_ctor_set_uint8(v___x_681_, 13, v___x_671_);
lean_ctor_set_uint8(v___x_681_, 14, v___x_680_);
lean_ctor_set_uint8(v___x_681_, 15, v___x_671_);
lean_ctor_set_uint8(v___x_681_, 16, v___x_671_);
lean_ctor_set_uint8(v___x_681_, 17, v___x_671_);
lean_ctor_set_uint8(v___x_681_, 18, v___x_671_);
lean_ctor_set_uint8(v___x_681_, 19, v___x_670_);
v___x_682_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_681_);
v___x_683_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set_uint64(v___x_683_, sizeof(void*)*1, v___x_682_);
v___x_684_ = lean_unsigned_to_nat(0u);
v___x_685_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__10, &l_Lean_Compiler_LCNF_toDecl___closed__10_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__10);
v___x_686_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__11));
v___x_687_ = lean_box(0);
v___x_688_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_688_, 0, v___x_683_);
lean_ctor_set(v___x_688_, 1, v___x_613_);
lean_ctor_set(v___x_688_, 2, v___x_685_);
lean_ctor_set(v___x_688_, 3, v___x_686_);
lean_ctor_set(v___x_688_, 4, v___x_687_);
lean_ctor_set(v___x_688_, 5, v___x_684_);
lean_ctor_set(v___x_688_, 6, v___x_687_);
lean_ctor_set_uint8(v___x_688_, sizeof(void*)*7, v___x_670_);
lean_ctor_set_uint8(v___x_688_, sizeof(void*)*7 + 1, v___x_670_);
lean_ctor_set_uint8(v___x_688_, sizeof(void*)*7 + 2, v___x_670_);
lean_ctor_set_uint8(v___x_688_, sizeof(void*)*7 + 3, v___x_671_);
v___x_689_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__19, &l_Lean_Compiler_LCNF_toDecl___closed__19_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__19);
v___x_690_ = lean_st_mk_ref(v___x_689_);
v___x_691_ = l_Lean_Compiler_LCNF_toLCNFType(v___x_677_, v___x_688_, v___x_690_, v_a_505_, v_a_506_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_693_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
lean_dec_ref_known(v___x_691_, 1);
v___x_693_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg(v_val_673_, v___f_676_, v___x_670_, v___x_688_, v___x_690_, v_a_505_, v_a_506_);
lean_dec_ref_known(v___x_688_, 7);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_693_, 1);
v___x_695_ = lean_st_ref_get(v___x_690_);
lean_dec(v___x_690_);
lean_dec(v___x_695_);
lean_inc(v_a_692_);
v___x_696_ = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(v_a_694_, v_a_692_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_696_, 1);
if (lean_obj_tag(v_a_697_) == 1)
{
lean_object* v_k_698_; 
v_k_698_ = lean_ctor_get(v_a_697_, 1);
lean_inc_ref(v_k_698_);
if (lean_obj_tag(v_k_698_) == 5)
{
lean_object* v_decl_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_722_; 
v_decl_699_ = lean_ctor_get(v_a_697_, 0);
lean_inc_ref(v_decl_699_);
lean_dec_ref_known(v_a_697_, 2);
v_isSharedCheck_722_ = !lean_is_exclusive(v_k_698_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; 
v_unused_723_ = lean_ctor_get(v_k_698_, 0);
lean_dec(v_unused_723_);
v___x_701_ = v_k_698_;
v_isShared_702_ = v_isSharedCheck_722_;
goto v_resetjp_700_;
}
else
{
lean_dec(v_k_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_722_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
uint8_t v___x_703_; lean_object* v___x_704_; 
v___x_703_ = 0;
v___x_704_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v___x_703_, v_decl_699_, v___x_670_, v_a_504_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_params_705_; lean_object* v_value_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; lean_object* v___x_711_; 
lean_dec_ref_known(v___x_704_, 1);
v_params_705_ = lean_ctor_get(v_decl_699_, 2);
lean_inc_ref(v_params_705_);
v_value_706_ = lean_ctor_get(v_decl_699_, 4);
lean_inc_ref(v_value_706_);
lean_dec_ref(v_decl_699_);
v___x_707_ = l_Lean_ConstantInfo_levelParams(v_val_618_);
lean_dec(v_val_618_);
v___x_708_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_708_, 0, v___y_615_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
lean_ctor_set(v___x_708_, 2, v_a_692_);
lean_ctor_set(v___x_708_, 3, v_params_705_);
v___x_709_ = lean_unbox(v_a_620_);
lean_dec(v_a_620_);
lean_ctor_set_uint8(v___x_708_, sizeof(void*)*4, v___x_709_);
if (v_isShared_702_ == 0)
{
lean_ctor_set_tag(v___x_701_, 0);
lean_ctor_set(v___x_701_, 0, v_value_706_);
v___x_711_ = v___x_701_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_value_706_);
v___x_711_ = v_reuseFailAlloc_713_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_712_; 
v___x_712_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_712_, 0, v___x_708_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
lean_ctor_set(v___x_712_, 2, v___x_623_);
lean_ctor_set_uint8(v___x_712_, sizeof(void*)*3, v___x_670_);
v___y_543_ = v___x_684_;
v___y_544_ = v___x_670_;
v___y_545_ = v_env_622_;
v_decl_546_ = v___x_712_;
v___y_547_ = v_a_503_;
v___y_548_ = v_a_504_;
v___y_549_ = v_a_505_;
v___y_550_ = v_a_506_;
goto v___jp_542_;
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_del_object(v___x_701_);
lean_dec_ref(v_decl_699_);
lean_dec(v_a_692_);
lean_dec(v___x_623_);
lean_dec_ref(v_env_622_);
lean_dec(v_a_620_);
lean_dec(v_val_618_);
lean_dec(v___y_615_);
v_a_714_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_704_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_704_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
else
{
uint8_t v___x_724_; 
lean_dec_ref(v_k_698_);
v___x_724_ = lean_unbox(v_a_620_);
lean_dec(v_a_620_);
v___y_595_ = v___y_615_;
v___y_596_ = v___x_684_;
v___y_597_ = v_a_692_;
v___y_598_ = v___x_670_;
v___y_599_ = v_val_618_;
v___y_600_ = v___x_724_;
v___y_601_ = v_a_697_;
v___y_602_ = v___x_623_;
v___y_603_ = v_env_622_;
v___y_604_ = v_a_503_;
v___y_605_ = v_a_504_;
v___y_606_ = v_a_505_;
v___y_607_ = v_a_506_;
goto v___jp_594_;
}
}
else
{
uint8_t v___x_725_; 
v___x_725_ = lean_unbox(v_a_620_);
lean_dec(v_a_620_);
v___y_595_ = v___y_615_;
v___y_596_ = v___x_684_;
v___y_597_ = v_a_692_;
v___y_598_ = v___x_670_;
v___y_599_ = v_val_618_;
v___y_600_ = v___x_725_;
v___y_601_ = v_a_697_;
v___y_602_ = v___x_623_;
v___y_603_ = v_env_622_;
v___y_604_ = v_a_503_;
v___y_605_ = v_a_504_;
v___y_606_ = v_a_505_;
v___y_607_ = v_a_506_;
goto v___jp_594_;
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_dec(v_a_692_);
lean_dec(v___x_623_);
lean_dec_ref(v_env_622_);
lean_dec(v_a_620_);
lean_dec(v_val_618_);
lean_dec(v___y_615_);
v_a_726_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_696_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_696_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec(v_a_692_);
lean_dec(v___x_690_);
lean_dec(v___x_623_);
lean_dec_ref(v_env_622_);
lean_dec(v_a_620_);
lean_dec(v_val_618_);
lean_dec(v___y_615_);
v_a_734_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_693_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_693_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec(v___x_690_);
lean_dec_ref_known(v___x_688_, 7);
lean_dec_ref(v___f_676_);
lean_dec(v_val_673_);
lean_dec(v___x_623_);
lean_dec_ref(v_env_622_);
lean_dec(v_a_620_);
lean_dec(v_val_618_);
lean_dec(v___y_615_);
v_a_742_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_691_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_691_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_dec(v___x_672_);
lean_dec(v___x_623_);
lean_dec_ref(v_env_622_);
lean_dec(v_a_620_);
lean_dec(v_val_618_);
v___x_750_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__21, &l_Lean_Compiler_LCNF_toDecl___closed__21_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__21);
v___x_751_ = l_Lean_MessageData_ofConstName(v___y_615_, v___x_670_);
v___x_752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_750_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__23, &l_Lean_Compiler_LCNF_toDecl___closed__23_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__23);
v___x_754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_752_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___x_754_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
return v___x_755_;
}
}
else
{
lean_object* v___x_756_; uint8_t v___x_757_; uint8_t v___x_758_; uint8_t v___x_759_; uint8_t v___x_760_; lean_object* v___x_761_; uint64_t v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
lean_dec_ref(v_env_622_);
v___x_756_ = l_Lean_ConstantInfo_type(v_val_618_);
v___x_757_ = 0;
v___x_758_ = 1;
v___x_759_ = 0;
v___x_760_ = 2;
v___x_761_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_761_, 0, v___x_757_);
lean_ctor_set_uint8(v___x_761_, 1, v___x_757_);
lean_ctor_set_uint8(v___x_761_, 2, v___x_757_);
lean_ctor_set_uint8(v___x_761_, 3, v___x_757_);
lean_ctor_set_uint8(v___x_761_, 4, v___x_757_);
lean_ctor_set_uint8(v___x_761_, 5, v___x_670_);
lean_ctor_set_uint8(v___x_761_, 6, v___x_670_);
lean_ctor_set_uint8(v___x_761_, 7, v___x_757_);
lean_ctor_set_uint8(v___x_761_, 8, v___x_670_);
lean_ctor_set_uint8(v___x_761_, 9, v___x_758_);
lean_ctor_set_uint8(v___x_761_, 10, v___x_759_);
lean_ctor_set_uint8(v___x_761_, 11, v___x_670_);
lean_ctor_set_uint8(v___x_761_, 12, v___x_670_);
lean_ctor_set_uint8(v___x_761_, 13, v___x_670_);
lean_ctor_set_uint8(v___x_761_, 14, v___x_760_);
lean_ctor_set_uint8(v___x_761_, 15, v___x_670_);
lean_ctor_set_uint8(v___x_761_, 16, v___x_670_);
lean_ctor_set_uint8(v___x_761_, 17, v___x_670_);
lean_ctor_set_uint8(v___x_761_, 18, v___x_670_);
lean_ctor_set_uint8(v___x_761_, 19, v___x_757_);
v___x_762_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_761_);
v___x_763_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_763_, 0, v___x_761_);
lean_ctor_set_uint64(v___x_763_, sizeof(void*)*1, v___x_762_);
v___x_764_ = lean_unsigned_to_nat(0u);
v___x_765_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__10, &l_Lean_Compiler_LCNF_toDecl___closed__10_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__10);
v___x_766_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__11));
v___x_767_ = lean_box(0);
v___x_768_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_768_, 0, v___x_763_);
lean_ctor_set(v___x_768_, 1, v___x_613_);
lean_ctor_set(v___x_768_, 2, v___x_765_);
lean_ctor_set(v___x_768_, 3, v___x_766_);
lean_ctor_set(v___x_768_, 4, v___x_767_);
lean_ctor_set(v___x_768_, 5, v___x_764_);
lean_ctor_set(v___x_768_, 6, v___x_767_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*7, v___x_757_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*7 + 1, v___x_757_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*7 + 2, v___x_757_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*7 + 3, v___x_671_);
v___x_769_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__19, &l_Lean_Compiler_LCNF_toDecl___closed__19_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__19);
v___x_770_ = lean_st_mk_ref(v___x_769_);
v___x_771_ = l_Lean_Compiler_LCNF_toLCNFType(v___x_756_, v___x_768_, v___x_770_, v_a_505_, v_a_506_);
lean_dec_ref_known(v___x_768_, 7);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc_n(v_a_772_, 2);
lean_dec_ref_known(v___x_771_, 1);
v___x_773_ = lean_st_ref_get(v___x_770_);
lean_dec(v___x_770_);
lean_dec(v___x_773_);
v___x_774_ = l_Lean_Compiler_LCNF_toDecl___lam__0(v_a_772_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_787_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_787_ == 0)
{
v___x_777_ = v___x_774_;
v_isShared_778_ = v_isSharedCheck_787_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_787_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_779_ = l_Lean_ConstantInfo_levelParams(v_val_618_);
lean_dec(v_val_618_);
v___x_780_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_780_, 0, v___y_615_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
lean_ctor_set(v___x_780_, 2, v_a_772_);
lean_ctor_set(v___x_780_, 3, v_a_775_);
v___x_781_ = lean_unbox(v_a_620_);
lean_dec(v_a_620_);
lean_ctor_set_uint8(v___x_780_, sizeof(void*)*4, v___x_781_);
v___x_782_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__24));
v___x_783_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_783_, 0, v___x_780_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
lean_ctor_set(v___x_783_, 2, v___x_623_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*3, v___x_757_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_783_);
v___x_785_ = v___x_777_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec(v_a_772_);
lean_dec(v___x_623_);
lean_dec(v_a_620_);
lean_dec(v_val_618_);
lean_dec(v___y_615_);
v_a_788_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_774_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_774_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec(v___x_770_);
lean_dec(v___x_623_);
lean_dec(v_a_620_);
lean_dec(v_val_618_);
lean_dec(v___y_615_);
v_a_796_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_771_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_771_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
}
else
{
lean_object* v___x_804_; uint8_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec(v_a_617_);
v___x_804_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__21, &l_Lean_Compiler_LCNF_toDecl___closed__21_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__21);
v___x_805_ = 0;
v___x_806_ = l_Lean_MessageData_ofConstName(v___y_615_, v___x_805_);
v___x_807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_804_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__26, &l_Lean_Compiler_LCNF_toDecl___closed__26_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__26);
v___x_809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_807_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___x_809_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
return v___x_810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___boxed(lean_object* v_declName_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_Compiler_LCNF_toDecl(v_declName_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1(uint8_t v___x_820_, lean_object* v_inst_821_, lean_object* v_a_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_820_, v_a_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___boxed(lean_object* v___x_829_, lean_object* v_inst_830_, lean_object* v_a_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
uint8_t v___x_15311__boxed_837_; lean_object* v_res_838_; 
v___x_15311__boxed_837_ = lean_unbox(v___x_829_);
v_res_838_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1(v___x_15311__boxed_837_, v_inst_830_, v_a_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2(lean_object* v_00_u03b2_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__14, &l_Lean_Compiler_LCNF_toDecl___closed__14_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__14);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__14, &l_Lean_Compiler_LCNF_toDecl___closed__14_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__14);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___boxed(lean_object* v___dummy_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg();
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2(lean_object* v_00_u03b2_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__14, &l_Lean_Compiler_LCNF_toDecl___closed__14_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__14);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__5(uint8_t v___x_847_, size_t v_sz_848_, size_t v_i_849_, lean_object* v_bs_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v___x_847_, v_sz_848_, v_i_849_, v_bs_850_, v___y_852_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__5___boxed(lean_object* v___x_857_, lean_object* v_sz_858_, lean_object* v_i_859_, lean_object* v_bs_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
uint8_t v___x_15343__boxed_866_; size_t v_sz_boxed_867_; size_t v_i_boxed_868_; lean_object* v_res_869_; 
v___x_15343__boxed_866_ = lean_unbox(v___x_857_);
v_sz_boxed_867_ = lean_unbox_usize(v_sz_858_);
lean_dec(v_sz_858_);
v_i_boxed_868_ = lean_unbox_usize(v_i_859_);
lean_dec(v_i_859_);
v_res_869_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__5(v___x_15343__boxed_866_, v_sz_boxed_867_, v_i_boxed_868_, v_bs_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
return v_res_869_;
}
}
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ToLCNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ExportAttr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ToDecl(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ToLCNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ExportAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ToDecl(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ToLCNF(uint8_t builtin);
lean_object* initialize_Lean_Compiler_Options(uint8_t builtin);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ExportAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ToDecl(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToLCNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExportAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ToDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ToDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ToDecl(builtin);
}
#ifdef __cplusplus
}
#endif
