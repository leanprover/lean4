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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
static const lean_string_object l_Lean_Compiler_LCNF_toDecl___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declaration `"};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__19 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__19_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__20;
static const lean_string_object l_Lean_Compiler_LCNF_toDecl___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "` does not have a value"};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__21 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__21_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__22;
static const lean_ctor_object l_Lean_Compiler_LCNF_toDecl___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__23 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__23_value;
static const lean_string_object l_Lean_Compiler_LCNF_toDecl___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "` not found"};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__24 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__24_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__25;
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
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_102_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_103_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__1);
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
lean_ctor_set(v___x_105_, 2, v___x_104_);
lean_ctor_set(v___x_105_, 3, v___x_104_);
lean_ctor_set(v___x_105_, 4, v___x_103_);
lean_ctor_set(v___x_105_, 5, v___x_103_);
lean_ctor_set(v___x_105_, 6, v___x_103_);
lean_ctor_set(v___x_105_, 7, v___x_103_);
lean_ctor_set(v___x_105_, 8, v___x_103_);
lean_ctor_set(v___x_105_, 9, v___x_103_);
lean_ctor_set(v___x_105_, 10, v___x_103_);
lean_ctor_set(v___x_105_, 11, v___x_102_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(lean_object* v_msg_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_ref_112_; lean_object* v___x_113_; lean_object* v_env_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v_ref_112_ = lean_ctor_get(v___y_109_, 2);
v___x_113_ = lean_st_ref_get(v___y_110_);
v_env_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc_ref(v_env_114_);
lean_dec(v___x_113_);
v___x_115_ = lean_st_ref_get(v___y_108_);
v___x_116_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_107_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_139_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_139_ == 0)
{
v___x_119_ = v___x_116_;
v_isShared_120_ = v_isSharedCheck_139_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_116_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_139_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v_lctx_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_137_; 
v_lctx_121_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_137_ == 0)
{
lean_object* v_unused_138_; 
v_unused_138_ = lean_ctor_get(v___x_115_, 1);
lean_dec(v_unused_138_);
v___x_123_ = v___x_115_;
v_isShared_124_ = v_isSharedCheck_137_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_lctx_121_);
lean_dec(v___x_115_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_137_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
uint8_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_125_ = lean_unbox(v_a_117_);
lean_dec(v_a_117_);
v___x_126_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_121_, v___x_125_);
lean_dec_ref(v_lctx_121_);
v___x_127_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_109_);
v___x_128_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__2, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__2_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__2);
v___x_129_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_129_, 0, v_env_114_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
lean_ctor_set(v___x_129_, 2, v___x_126_);
lean_ctor_set(v___x_129_, 3, v___x_127_);
if (v_isShared_124_ == 0)
{
lean_ctor_set_tag(v___x_123_, 3);
lean_ctor_set(v___x_123_, 1, v_msg_106_);
lean_ctor_set(v___x_123_, 0, v___x_129_);
v___x_131_ = v___x_123_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_msg_106_);
v___x_131_ = v_reuseFailAlloc_136_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; lean_object* v___x_134_; 
lean_inc(v_ref_112_);
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v_ref_112_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
if (v_isShared_120_ == 0)
{
lean_ctor_set_tag(v___x_119_, 1);
lean_ctor_set(v___x_119_, 0, v___x_132_);
v___x_134_ = v___x_119_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
lean_dec(v___x_115_);
lean_dec_ref(v_env_114_);
lean_dec_ref(v_msg_106_);
v_a_140_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_116_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_116_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___boxed(lean_object* v_msg_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v_msg_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4(lean_object* v_00_u03b1_155_, lean_object* v_msg_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v_msg_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___boxed(lean_object* v_00_u03b1_163_, lean_object* v_msg_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4(v_00_u03b1_163_, v_msg_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg___lam__0(lean_object* v_k_171_, lean_object* v_b_172_, lean_object* v_c_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v___x_179_; 
lean_inc(v___y_177_);
lean_inc_ref(v___y_176_);
lean_inc(v___y_175_);
lean_inc_ref(v___y_174_);
v___x_179_ = lean_apply_7(v_k_171_, v_b_172_, v_c_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, lean_box(0));
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg___lam__0___boxed(lean_object* v_k_180_, lean_object* v_b_181_, lean_object* v_c_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg___lam__0(v_k_180_, v_b_181_, v_c_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg(lean_object* v_e_189_, lean_object* v_k_190_, uint8_t v_cleanupAnnotations_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v___f_197_; uint8_t v___x_198_; uint8_t v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___f_197_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_197_, 0, v_k_190_);
v___x_198_ = 1;
v___x_199_ = 0;
v___x_200_ = lean_box(0);
v___x_201_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_189_, v___x_198_, v___x_199_, v___x_198_, v___x_199_, v___x_200_, v___f_197_, v_cleanupAnnotations_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
v_a_210_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_201_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_201_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg___boxed(lean_object* v_e_218_, lean_object* v_k_219_, lean_object* v_cleanupAnnotations_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_226_; lean_object* v_res_227_; 
v_cleanupAnnotations_boxed_226_ = lean_unbox(v_cleanupAnnotations_220_);
v_res_227_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg(v_e_218_, v_k_219_, v_cleanupAnnotations_boxed_226_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6(lean_object* v_00_u03b1_228_, lean_object* v_e_229_, lean_object* v_k_230_, uint8_t v_cleanupAnnotations_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg(v_e_229_, v_k_230_, v_cleanupAnnotations_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___boxed(lean_object* v_00_u03b1_238_, lean_object* v_e_239_, lean_object* v_k_240_, lean_object* v_cleanupAnnotations_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_247_; lean_object* v_res_248_; 
v_cleanupAnnotations_boxed_247_ = lean_unbox(v_cleanupAnnotations_241_);
v_res_248_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6(v_00_u03b1_238_, v_e_239_, v_k_240_, v_cleanupAnnotations_boxed_247_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(uint8_t v___x_249_, lean_object* v_a_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_snd_256_; 
v_snd_256_ = lean_ctor_get(v_a_250_, 1);
lean_inc(v_snd_256_);
if (lean_obj_tag(v_snd_256_) == 7)
{
lean_object* v_fst_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_284_; 
v_fst_257_ = lean_ctor_get(v_a_250_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v_a_250_);
if (v_isSharedCheck_284_ == 0)
{
lean_object* v_unused_285_; 
v_unused_285_ = lean_ctor_get(v_a_250_, 1);
lean_dec(v_unused_285_);
v___x_259_ = v_a_250_;
v_isShared_260_ = v_isSharedCheck_284_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_fst_257_);
lean_dec(v_a_250_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_284_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v_binderName_261_; lean_object* v_binderType_262_; lean_object* v_body_263_; uint8_t v___y_265_; 
v_binderName_261_ = lean_ctor_get(v_snd_256_, 0);
lean_inc(v_binderName_261_);
v_binderType_262_ = lean_ctor_get(v_snd_256_, 1);
lean_inc_ref(v_binderType_262_);
v_body_263_ = lean_ctor_get(v_snd_256_, 2);
lean_inc_ref(v_body_263_);
lean_dec_ref_known(v_snd_256_, 3);
if (v___x_249_ == 0)
{
uint8_t v___x_282_; 
v___x_282_ = l_Lean_isMarkedBorrowed(v_binderType_262_);
v___y_265_ = v___x_282_;
goto v___jp_264_;
}
else
{
uint8_t v___x_283_; 
v___x_283_ = 0;
v___y_265_ = v___x_283_;
goto v___jp_264_;
}
v___jp_264_:
{
uint8_t v___x_266_; lean_object* v___x_267_; 
v___x_266_ = 0;
v___x_267_ = l_Lean_Compiler_LCNF_mkParam(v___x_266_, v_binderName_261_, v_binderType_262_, v___y_265_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_268_);
lean_dec_ref_known(v___x_267_, 1);
v___x_269_ = lean_array_push(v_fst_257_, v_a_268_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 1, v_body_263_);
lean_ctor_set(v___x_259_, 0, v___x_269_);
v___x_271_ = v___x_259_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_body_263_);
v___x_271_ = v_reuseFailAlloc_273_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
v_a_250_ = v___x_271_;
goto _start;
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_dec_ref(v_body_263_);
lean_del_object(v___x_259_);
lean_dec(v_fst_257_);
v_a_274_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_267_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_267_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
}
else
{
lean_object* v_fst_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_294_; 
v_fst_286_ = lean_ctor_get(v_a_250_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v_a_250_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; 
v_unused_295_ = lean_ctor_get(v_a_250_, 1);
lean_dec(v_unused_295_);
v___x_288_ = v_a_250_;
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_fst_286_);
lean_dec(v_a_250_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_fst_286_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_snd_256_);
v___x_291_ = v_reuseFailAlloc_293_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_292_; 
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg___boxed(lean_object* v___x_296_, lean_object* v_a_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
uint8_t v___x_13977__boxed_303_; lean_object* v_res_304_; 
v___x_13977__boxed_303_ = lean_unbox(v___x_296_);
v_res_304_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_13977__boxed_303_, v_a_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0(lean_object* v_expr_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_313_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0));
v___x_314_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_310_);
v___x_315_ = l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
v___x_316_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(v___x_314_, v___x_315_);
lean_dec_ref(v___x_314_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_313_);
lean_ctor_set(v___x_317_, 1, v_expr_307_);
v___x_318_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_316_, v___x_317_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_327_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_327_ == 0)
{
v___x_321_ = v___x_318_;
v_isShared_322_ = v_isSharedCheck_327_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_318_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_327_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v_fst_323_; lean_object* v___x_325_; 
v_fst_323_ = lean_ctor_get(v_a_319_, 0);
lean_inc(v_fst_323_);
lean_dec(v_a_319_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v_fst_323_);
v___x_325_ = v___x_321_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_fst_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
v_a_328_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_318_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_318_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0___boxed(lean_object* v_expr_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Compiler_LCNF_toDecl___lam__0(v_expr_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1(uint8_t v___x_343_, uint8_t v___x_344_, lean_object* v_xs_345_, lean_object* v_body_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_Meta_etaExpand(v_body_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; uint8_t v___x_354_; lean_object* v___x_355_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_353_);
lean_dec_ref_known(v___x_352_, 1);
v___x_354_ = 1;
v___x_355_ = l_Lean_Meta_mkLambdaFVars(v_xs_345_, v_a_353_, v___x_343_, v___x_344_, v___x_343_, v___x_344_, v___x_354_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
return v___x_355_;
}
else
{
return v___x_352_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1___boxed(lean_object* v___x_356_, lean_object* v___x_357_, lean_object* v_xs_358_, lean_object* v_body_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
uint8_t v___x_14135__boxed_365_; uint8_t v___x_14136__boxed_366_; lean_object* v_res_367_; 
v___x_14135__boxed_365_ = lean_unbox(v___x_356_);
v___x_14136__boxed_366_ = lean_unbox(v___x_357_);
v_res_367_ = l_Lean_Compiler_LCNF_toDecl___lam__1(v___x_14135__boxed_365_, v___x_14136__boxed_366_, v_xs_358_, v_body_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec_ref(v_xs_358_);
return v_res_367_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(lean_object* v_as_368_, size_t v_i_369_, size_t v_stop_370_){
_start:
{
uint8_t v___x_371_; 
v___x_371_ = lean_usize_dec_eq(v_i_369_, v_stop_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; uint8_t v_borrow_373_; 
v___x_372_ = lean_array_uget_borrowed(v_as_368_, v_i_369_);
v_borrow_373_ = lean_ctor_get_uint8(v___x_372_, sizeof(void*)*3);
if (v_borrow_373_ == 0)
{
size_t v___x_374_; size_t v___x_375_; 
v___x_374_ = ((size_t)1ULL);
v___x_375_ = lean_usize_add(v_i_369_, v___x_374_);
v_i_369_ = v___x_375_;
goto _start;
}
else
{
return v_borrow_373_;
}
}
else
{
uint8_t v___x_377_; 
v___x_377_ = 0;
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3___boxed(lean_object* v_as_378_, lean_object* v_i_379_, lean_object* v_stop_380_){
_start:
{
size_t v_i_boxed_381_; size_t v_stop_boxed_382_; uint8_t v_res_383_; lean_object* v_r_384_; 
v_i_boxed_381_ = lean_unbox_usize(v_i_379_);
lean_dec(v_i_379_);
v_stop_boxed_382_ = lean_unbox_usize(v_stop_380_);
lean_dec(v_stop_380_);
v_res_383_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(v_as_378_, v_i_boxed_381_, v_stop_boxed_382_);
lean_dec_ref(v_as_378_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__0);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2___redArg(){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2___redArg___closed__0);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2___redArg___boxed(lean_object* v___dummy_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2___redArg();
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(uint8_t v___x_391_, size_t v_sz_392_, size_t v_i_393_, lean_object* v_bs_394_, lean_object* v___y_395_){
_start:
{
uint8_t v___x_397_; 
v___x_397_ = lean_usize_dec_lt(v_i_393_, v_sz_392_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; 
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v_bs_394_);
return v___x_398_;
}
else
{
lean_object* v_v_399_; lean_object* v___x_400_; lean_object* v_bs_x27_401_; uint8_t v___x_402_; lean_object* v___x_403_; 
v_v_399_ = lean_array_uget(v_bs_394_, v_i_393_);
v___x_400_ = lean_unsigned_to_nat(0u);
v_bs_x27_401_ = lean_array_uset(v_bs_394_, v_i_393_, v___x_400_);
v___x_402_ = 0;
v___x_403_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v___x_402_, v_v_399_, v___x_391_, v___y_395_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; size_t v___x_405_; size_t v___x_406_; lean_object* v___x_407_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_404_);
lean_dec_ref_known(v___x_403_, 1);
v___x_405_ = ((size_t)1ULL);
v___x_406_ = lean_usize_add(v_i_393_, v___x_405_);
v___x_407_ = lean_array_uset(v_bs_x27_401_, v_i_393_, v_a_404_);
v_i_393_ = v___x_406_;
v_bs_394_ = v___x_407_;
goto _start;
}
else
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
lean_dec_ref(v_bs_x27_401_);
v_a_409_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_403_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_403_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___boxed(lean_object* v___x_417_, lean_object* v_sz_418_, lean_object* v_i_419_, lean_object* v_bs_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
uint8_t v___x_14186__boxed_423_; size_t v_sz_boxed_424_; size_t v_i_boxed_425_; lean_object* v_res_426_; 
v___x_14186__boxed_423_ = lean_unbox(v___x_417_);
v_sz_boxed_424_ = lean_unbox_usize(v_sz_418_);
lean_dec(v_sz_418_);
v_i_boxed_425_ = lean_unbox_usize(v_i_419_);
lean_dec(v_i_419_);
v_res_426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v___x_14186__boxed_423_, v_sz_boxed_424_, v_i_boxed_425_, v_bs_420_, v___y_421_);
lean_dec(v___y_421_);
return v_res_426_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__1(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__0));
v___x_429_ = l_Lean_stringToMessageData(v___x_428_);
return v___x_429_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__3(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__2));
v___x_432_ = l_Lean_stringToMessageData(v___x_431_);
return v___x_432_;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_toDecl___closed__5(void){
_start:
{
lean_object* v___x_439_; uint64_t v___x_440_; 
v___x_439_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__4));
v___x_440_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_439_);
return v___x_440_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__6(void){
_start:
{
uint64_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_441_ = lean_uint64_once(&l_Lean_Compiler_LCNF_toDecl___closed__5, &l_Lean_Compiler_LCNF_toDecl___closed__5_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__5);
v___x_442_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__4));
v___x_443_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_443_, 0, v___x_442_);
lean_ctor_set_uint64(v___x_443_, sizeof(void*)*1, v___x_441_);
return v___x_443_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__7(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___closed__0);
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__8(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = lean_unsigned_to_nat(32u);
v___x_447_ = lean_mk_empty_array_with_capacity(v___x_446_);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__9(void){
_start:
{
size_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_449_ = ((size_t)5ULL);
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_unsigned_to_nat(32u);
v___x_452_ = lean_mk_empty_array_with_capacity(v___x_451_);
v___x_453_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__8, &l_Lean_Compiler_LCNF_toDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__8);
v___x_454_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_454_, 0, v___x_453_);
lean_ctor_set(v___x_454_, 1, v___x_452_);
lean_ctor_set(v___x_454_, 2, v___x_450_);
lean_ctor_set(v___x_454_, 3, v___x_450_);
lean_ctor_set_usize(v___x_454_, 4, v___x_449_);
return v___x_454_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__10(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_455_ = lean_box(1);
v___x_456_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__9, &l_Lean_Compiler_LCNF_toDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__9);
v___x_457_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__7, &l_Lean_Compiler_LCNF_toDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__7);
v___x_458_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
lean_ctor_set(v___x_458_, 2, v___x_455_);
return v___x_458_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__12(void){
_start:
{
uint8_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_461_ = 1;
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_box(0);
v___x_464_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__11));
v___x_465_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__10, &l_Lean_Compiler_LCNF_toDecl___closed__10_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__10);
v___x_466_ = lean_box(1);
v___x_467_ = 0;
v___x_468_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__6, &l_Lean_Compiler_LCNF_toDecl___closed__6_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__6);
v___x_469_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v___x_466_);
lean_ctor_set(v___x_469_, 2, v___x_465_);
lean_ctor_set(v___x_469_, 3, v___x_464_);
lean_ctor_set(v___x_469_, 4, v___x_463_);
lean_ctor_set(v___x_469_, 5, v___x_462_);
lean_ctor_set(v___x_469_, 6, v___x_463_);
lean_ctor_set_uint8(v___x_469_, sizeof(void*)*7, v___x_467_);
lean_ctor_set_uint8(v___x_469_, sizeof(void*)*7 + 1, v___x_467_);
lean_ctor_set_uint8(v___x_469_, sizeof(void*)*7 + 2, v___x_467_);
lean_ctor_set_uint8(v___x_469_, sizeof(void*)*7 + 3, v___x_461_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__13(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_470_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_471_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__7, &l_Lean_Compiler_LCNF_toDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__7);
v___x_472_ = lean_unsigned_to_nat(0u);
v___x_473_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
lean_ctor_set(v___x_473_, 2, v___x_472_);
lean_ctor_set(v___x_473_, 3, v___x_472_);
lean_ctor_set(v___x_473_, 4, v___x_471_);
lean_ctor_set(v___x_473_, 5, v___x_471_);
lean_ctor_set(v___x_473_, 6, v___x_471_);
lean_ctor_set(v___x_473_, 7, v___x_471_);
lean_ctor_set(v___x_473_, 8, v___x_471_);
lean_ctor_set(v___x_473_, 9, v___x_471_);
lean_ctor_set(v___x_473_, 10, v___x_471_);
lean_ctor_set(v___x_473_, 11, v___x_470_);
return v___x_473_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__14(void){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2___redArg();
return v___x_474_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__15(void){
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
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__16(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_478_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__15, &l_Lean_Compiler_LCNF_toDecl___closed__15_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__15);
v___x_479_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__7, &l_Lean_Compiler_LCNF_toDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__7);
v___x_480_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__14, &l_Lean_Compiler_LCNF_toDecl___closed__14_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__14);
v___x_481_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_479_);
lean_ctor_set(v___x_481_, 2, v___x_479_);
lean_ctor_set(v___x_481_, 3, v___x_479_);
lean_ctor_set(v___x_481_, 4, v___x_479_);
lean_ctor_set(v___x_481_, 5, v___x_479_);
lean_ctor_set(v___x_481_, 6, v___x_479_);
lean_ctor_set(v___x_481_, 7, v___x_478_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__17(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__7, &l_Lean_Compiler_LCNF_toDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__7);
v___x_483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
lean_ctor_set(v___x_483_, 2, v___x_482_);
lean_ctor_set(v___x_483_, 3, v___x_482_);
lean_ctor_set(v___x_483_, 4, v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__18(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_484_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__17, &l_Lean_Compiler_LCNF_toDecl___closed__17_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__17);
v___x_485_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__9, &l_Lean_Compiler_LCNF_toDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__9);
v___x_486_ = lean_box(1);
v___x_487_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__16, &l_Lean_Compiler_LCNF_toDecl___closed__16_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__16);
v___x_488_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__13, &l_Lean_Compiler_LCNF_toDecl___closed__13_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__13);
v___x_489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v___x_487_);
lean_ctor_set(v___x_489_, 2, v___x_486_);
lean_ctor_set(v___x_489_, 3, v___x_485_);
lean_ctor_set(v___x_489_, 4, v___x_484_);
return v___x_489_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__20(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__19));
v___x_492_ = l_Lean_stringToMessageData(v___x_491_);
return v___x_492_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__22(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__21));
v___x_495_ = l_Lean_stringToMessageData(v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__25(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__24));
v___x_500_ = l_Lean_stringToMessageData(v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object* v_declName_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v_decl_510_; lean_object* v_name_511_; lean_object* v_params_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_542_; lean_object* v___y_543_; uint8_t v___y_544_; lean_object* v_decl_545_; lean_object* v___y_546_; lean_object* v___y_547_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v___y_599_; uint8_t v___y_600_; lean_object* v___y_601_; uint8_t v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___x_612_; lean_object* v___y_614_; lean_object* v___x_810_; 
v___x_612_ = lean_box(1);
v___x_810_ = l_Lean_Compiler_isUnsafeRecName_x3f(v_declName_501_);
if (lean_obj_tag(v___x_810_) == 1)
{
lean_object* v_val_811_; 
lean_dec(v_declName_501_);
v_val_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_val_811_);
lean_dec_ref_known(v___x_810_, 1);
v___y_614_ = v_val_811_;
goto v___jp_613_;
}
else
{
lean_dec(v___x_810_);
v___y_614_ = v_declName_501_;
goto v___jp_613_;
}
v___jp_507_:
{
uint8_t v___x_517_; 
lean_inc(v_name_511_);
v___x_517_ = l_Lean_isExport(v___y_509_, v_name_511_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; 
lean_dec_ref(v_params_512_);
lean_dec(v_name_511_);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v_decl_510_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = lean_array_get_size(v_params_512_);
v___x_520_ = lean_nat_dec_lt(v___y_508_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; 
lean_dec_ref(v_params_512_);
lean_dec(v_name_511_);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v_decl_510_);
return v___x_521_;
}
else
{
if (v___x_520_ == 0)
{
lean_object* v___x_522_; 
lean_dec_ref(v_params_512_);
lean_dec(v_name_511_);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v_decl_510_);
return v___x_522_;
}
else
{
size_t v___x_523_; size_t v___x_524_; uint8_t v___x_525_; 
v___x_523_ = ((size_t)0ULL);
v___x_524_ = lean_usize_of_nat(v___x_519_);
v___x_525_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(v_params_512_, v___x_523_, v___x_524_);
lean_dec_ref(v_params_512_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; 
lean_dec(v_name_511_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v_decl_510_);
return v___x_526_;
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec_ref(v_decl_510_);
v___x_527_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__1, &l_Lean_Compiler_LCNF_toDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__1);
v___x_528_ = l_Lean_MessageData_ofName(v_name_511_);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__3, &l_Lean_Compiler_LCNF_toDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__3);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___x_531_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
v_a_533_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_532_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
}
}
v___jp_541_:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_Compiler_LCNF_Decl_etaExpand(v_decl_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_550_, 1);
v___x_552_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_548_);
v___x_553_ = l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
v___x_554_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(v___x_552_, v___x_553_);
lean_dec_ref(v___x_552_);
if (v___x_554_ == 0)
{
lean_object* v_toSignature_555_; lean_object* v_name_556_; lean_object* v_params_557_; 
v_toSignature_555_ = lean_ctor_get(v_a_551_, 0);
v_name_556_ = lean_ctor_get(v_toSignature_555_, 0);
lean_inc(v_name_556_);
v_params_557_ = lean_ctor_get(v_toSignature_555_, 3);
lean_inc_ref(v_params_557_);
v___y_508_ = v___y_542_;
v___y_509_ = v___y_543_;
v_decl_510_ = v_a_551_;
v_name_511_ = v_name_556_;
v_params_512_ = v_params_557_;
v___y_513_ = v___y_546_;
v___y_514_ = v___y_547_;
v___y_515_ = v___y_548_;
v___y_516_ = v___y_549_;
goto v___jp_507_;
}
else
{
lean_object* v_toSignature_558_; lean_object* v_value_559_; uint8_t v_recursive_560_; lean_object* v_inlineAttr_x3f_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_592_; 
v_toSignature_558_ = lean_ctor_get(v_a_551_, 0);
v_value_559_ = lean_ctor_get(v_a_551_, 1);
v_recursive_560_ = lean_ctor_get_uint8(v_a_551_, sizeof(void*)*3);
v_inlineAttr_x3f_561_ = lean_ctor_get(v_a_551_, 2);
v_isSharedCheck_592_ = !lean_is_exclusive(v_a_551_);
if (v_isSharedCheck_592_ == 0)
{
v___x_563_ = v_a_551_;
v_isShared_564_ = v_isSharedCheck_592_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_inlineAttr_x3f_561_);
lean_inc(v_value_559_);
lean_inc(v_toSignature_558_);
lean_dec(v_a_551_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_592_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v_name_565_; lean_object* v_levelParams_566_; lean_object* v_type_567_; lean_object* v_params_568_; uint8_t v_safe_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_591_; 
v_name_565_ = lean_ctor_get(v_toSignature_558_, 0);
v_levelParams_566_ = lean_ctor_get(v_toSignature_558_, 1);
v_type_567_ = lean_ctor_get(v_toSignature_558_, 2);
v_params_568_ = lean_ctor_get(v_toSignature_558_, 3);
v_safe_569_ = lean_ctor_get_uint8(v_toSignature_558_, sizeof(void*)*4);
v_isSharedCheck_591_ = !lean_is_exclusive(v_toSignature_558_);
if (v_isSharedCheck_591_ == 0)
{
v___x_571_ = v_toSignature_558_;
v_isShared_572_ = v_isSharedCheck_591_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_params_568_);
lean_inc(v_type_567_);
lean_inc(v_levelParams_566_);
lean_inc(v_name_565_);
lean_dec(v_toSignature_558_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_591_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
size_t v_sz_573_; size_t v___x_574_; lean_object* v___x_575_; 
v_sz_573_ = lean_array_size(v_params_568_);
v___x_574_ = ((size_t)0ULL);
v___x_575_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v___y_544_, v_sz_573_, v___x_574_, v_params_568_, v___y_547_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_578_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc_n(v_a_576_, 2);
lean_dec_ref_known(v___x_575_, 1);
lean_inc(v_name_565_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 3, v_a_576_);
v___x_578_ = v___x_571_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_name_565_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_levelParams_566_);
lean_ctor_set(v_reuseFailAlloc_582_, 2, v_type_567_);
lean_ctor_set(v_reuseFailAlloc_582_, 3, v_a_576_);
lean_ctor_set_uint8(v_reuseFailAlloc_582_, sizeof(void*)*4, v_safe_569_);
v___x_578_ = v_reuseFailAlloc_582_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_580_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_578_);
v___x_580_ = v___x_563_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_value_559_);
lean_ctor_set(v_reuseFailAlloc_581_, 2, v_inlineAttr_x3f_561_);
lean_ctor_set_uint8(v_reuseFailAlloc_581_, sizeof(void*)*3, v_recursive_560_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
v___y_508_ = v___y_542_;
v___y_509_ = v___y_543_;
v_decl_510_ = v___x_580_;
v_name_511_ = v_name_565_;
v_params_512_ = v_a_576_;
v___y_513_ = v___y_546_;
v___y_514_ = v___y_547_;
v___y_515_ = v___y_548_;
v___y_516_ = v___y_549_;
goto v___jp_507_;
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_del_object(v___x_571_);
lean_dec_ref(v_type_567_);
lean_dec(v_levelParams_566_);
lean_dec(v_name_565_);
lean_del_object(v___x_563_);
lean_dec(v_inlineAttr_x3f_561_);
lean_dec_ref(v_value_559_);
lean_dec_ref(v___y_543_);
v_a_583_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_575_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_575_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_543_);
return v___x_550_;
}
}
v___jp_593_:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_607_ = l_Lean_ConstantInfo_levelParams(v___y_598_);
lean_dec_ref(v___y_598_);
v___x_608_ = lean_mk_empty_array_with_capacity(v___y_597_);
v___x_609_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_609_, 0, v___y_594_);
lean_ctor_set(v___x_609_, 1, v___x_607_);
lean_ctor_set(v___x_609_, 2, v___y_601_);
lean_ctor_set(v___x_609_, 3, v___x_608_);
lean_ctor_set_uint8(v___x_609_, sizeof(void*)*4, v___y_600_);
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v___y_596_);
v___x_611_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_611_, 0, v___x_609_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
lean_ctor_set(v___x_611_, 2, v___y_595_);
lean_ctor_set_uint8(v___x_611_, sizeof(void*)*3, v___y_602_);
v___y_542_ = v___y_597_;
v___y_543_ = v___y_599_;
v___y_544_ = v___y_602_;
v_decl_545_ = v___x_611_;
v___y_546_ = v___y_603_;
v___y_547_ = v___y_604_;
v___y_548_ = v___y_605_;
v___y_549_ = v___y_606_;
goto v___jp_541_;
}
v___jp_613_:
{
lean_object* v___x_615_; lean_object* v_a_616_; 
lean_inc(v___y_614_);
v___x_615_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(v___y_614_, v_a_505_);
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
lean_dec_ref(v___x_615_);
if (lean_obj_tag(v_a_616_) == 1)
{
lean_object* v_val_617_; lean_object* v___x_618_; lean_object* v_a_619_; lean_object* v___x_620_; lean_object* v_env_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_val_617_ = lean_ctor_get(v_a_616_, 0);
lean_inc(v_val_617_);
lean_dec_ref_known(v_a_616_, 1);
lean_inc_n(v___y_614_, 3);
v___x_618_ = l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(v___y_614_, v_a_505_);
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref(v___x_618_);
v___x_620_ = lean_st_ref_get(v_a_505_);
v_env_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc_ref_n(v_env_621_, 3);
lean_dec(v___x_620_);
v___x_622_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_621_, v___y_614_);
v___x_623_ = l_Lean_getExternAttrData_x3f(v_env_621_, v___y_614_);
if (lean_obj_tag(v___x_623_) == 1)
{
lean_object* v_val_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_668_; 
lean_dec_ref(v_env_621_);
v_val_624_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_668_ == 0)
{
v___x_626_ = v___x_623_;
v_isShared_627_ = v_isSharedCheck_668_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_val_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_668_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; uint8_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_628_ = l_Lean_ConstantInfo_type(v_val_617_);
v___x_629_ = 0;
v___x_630_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__12, &l_Lean_Compiler_LCNF_toDecl___closed__12_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__12);
v___x_631_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__18, &l_Lean_Compiler_LCNF_toDecl___closed__18_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__18);
v___x_632_ = lean_st_mk_ref(v___x_631_);
v___x_633_ = l_Lean_Compiler_LCNF_toLCNFType(v___x_628_, v___x_630_, v___x_632_, v_a_504_, v_a_505_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc_n(v_a_634_, 2);
lean_dec_ref_known(v___x_633_, 1);
v___x_635_ = lean_st_ref_get(v___x_632_);
lean_dec(v___x_632_);
lean_dec(v___x_635_);
v___x_636_ = l_Lean_Compiler_LCNF_toDecl___lam__0(v_a_634_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_651_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_651_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_651_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_651_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; lean_object* v___x_645_; 
v___x_641_ = l_Lean_ConstantInfo_levelParams(v_val_617_);
lean_dec(v_val_617_);
v___x_642_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_642_, 0, v___y_614_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
lean_ctor_set(v___x_642_, 2, v_a_634_);
lean_ctor_set(v___x_642_, 3, v_a_637_);
v___x_643_ = lean_unbox(v_a_619_);
lean_dec(v_a_619_);
lean_ctor_set_uint8(v___x_642_, sizeof(void*)*4, v___x_643_);
if (v_isShared_627_ == 0)
{
v___x_645_ = v___x_626_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_val_624_);
v___x_645_ = v_reuseFailAlloc_650_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_646_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_646_, 0, v___x_642_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
lean_ctor_set(v___x_646_, 2, v___x_622_);
lean_ctor_set_uint8(v___x_646_, sizeof(void*)*3, v___x_629_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v___x_646_);
v___x_648_ = v___x_639_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec(v_a_634_);
lean_del_object(v___x_626_);
lean_dec(v_val_624_);
lean_dec(v___x_622_);
lean_dec(v_a_619_);
lean_dec(v_val_617_);
lean_dec(v___y_614_);
v_a_652_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_636_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_636_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec(v___x_632_);
lean_del_object(v___x_626_);
lean_dec(v_val_624_);
lean_dec(v___x_622_);
lean_dec(v_a_619_);
lean_dec(v_val_617_);
lean_dec(v___y_614_);
v_a_660_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_633_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_633_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
else
{
uint8_t v___x_669_; uint8_t v___x_670_; 
lean_dec(v___x_623_);
lean_inc(v___y_614_);
lean_inc_ref(v_env_621_);
v___x_669_ = l_Lean_hasInitAttr(v_env_621_, v___y_614_);
v___x_670_ = 1;
if (v___x_669_ == 0)
{
lean_object* v___x_671_; 
lean_inc(v_val_617_);
v___x_671_ = l_Lean_ConstantInfo_value_x3f(v_val_617_, v___x_670_);
if (lean_obj_tag(v___x_671_) == 1)
{
lean_object* v_val_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___f_675_; lean_object* v___x_676_; uint8_t v___x_677_; uint8_t v___x_678_; uint8_t v___x_679_; lean_object* v___x_680_; uint64_t v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v_val_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_val_672_);
lean_dec_ref_known(v___x_671_, 1);
v___x_673_ = lean_box(v___x_669_);
v___x_674_ = lean_box(v___x_670_);
v___f_675_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toDecl___lam__1___boxed), 9, 2);
lean_closure_set(v___f_675_, 0, v___x_673_);
lean_closure_set(v___f_675_, 1, v___x_674_);
v___x_676_ = l_Lean_ConstantInfo_type(v_val_617_);
v___x_677_ = 1;
v___x_678_ = 0;
v___x_679_ = 2;
v___x_680_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_680_, 0, v___x_669_);
lean_ctor_set_uint8(v___x_680_, 1, v___x_669_);
lean_ctor_set_uint8(v___x_680_, 2, v___x_669_);
lean_ctor_set_uint8(v___x_680_, 3, v___x_669_);
lean_ctor_set_uint8(v___x_680_, 4, v___x_669_);
lean_ctor_set_uint8(v___x_680_, 5, v___x_670_);
lean_ctor_set_uint8(v___x_680_, 6, v___x_670_);
lean_ctor_set_uint8(v___x_680_, 7, v___x_669_);
lean_ctor_set_uint8(v___x_680_, 8, v___x_670_);
lean_ctor_set_uint8(v___x_680_, 9, v___x_677_);
lean_ctor_set_uint8(v___x_680_, 10, v___x_678_);
lean_ctor_set_uint8(v___x_680_, 11, v___x_670_);
lean_ctor_set_uint8(v___x_680_, 12, v___x_670_);
lean_ctor_set_uint8(v___x_680_, 13, v___x_670_);
lean_ctor_set_uint8(v___x_680_, 14, v___x_679_);
lean_ctor_set_uint8(v___x_680_, 15, v___x_670_);
lean_ctor_set_uint8(v___x_680_, 16, v___x_670_);
lean_ctor_set_uint8(v___x_680_, 17, v___x_670_);
lean_ctor_set_uint8(v___x_680_, 18, v___x_670_);
lean_ctor_set_uint8(v___x_680_, 19, v___x_669_);
v___x_681_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_680_);
v___x_682_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_682_, 0, v___x_680_);
lean_ctor_set_uint64(v___x_682_, sizeof(void*)*1, v___x_681_);
v___x_683_ = lean_unsigned_to_nat(0u);
v___x_684_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__10, &l_Lean_Compiler_LCNF_toDecl___closed__10_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__10);
v___x_685_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__11));
v___x_686_ = lean_box(0);
v___x_687_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_687_, 0, v___x_682_);
lean_ctor_set(v___x_687_, 1, v___x_612_);
lean_ctor_set(v___x_687_, 2, v___x_684_);
lean_ctor_set(v___x_687_, 3, v___x_685_);
lean_ctor_set(v___x_687_, 4, v___x_686_);
lean_ctor_set(v___x_687_, 5, v___x_683_);
lean_ctor_set(v___x_687_, 6, v___x_686_);
lean_ctor_set_uint8(v___x_687_, sizeof(void*)*7, v___x_669_);
lean_ctor_set_uint8(v___x_687_, sizeof(void*)*7 + 1, v___x_669_);
lean_ctor_set_uint8(v___x_687_, sizeof(void*)*7 + 2, v___x_669_);
lean_ctor_set_uint8(v___x_687_, sizeof(void*)*7 + 3, v___x_670_);
v___x_688_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__18, &l_Lean_Compiler_LCNF_toDecl___closed__18_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__18);
v___x_689_ = lean_st_mk_ref(v___x_688_);
v___x_690_ = l_Lean_Compiler_LCNF_toLCNFType(v___x_676_, v___x_687_, v___x_689_, v_a_504_, v_a_505_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_692_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref_known(v___x_690_, 1);
v___x_692_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__6___redArg(v_val_672_, v___f_675_, v___x_669_, v___x_687_, v___x_689_, v_a_504_, v_a_505_);
lean_dec_ref_known(v___x_687_, 7);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
v___x_694_ = lean_st_ref_get(v___x_689_);
lean_dec(v___x_689_);
lean_dec(v___x_694_);
lean_inc(v_a_691_);
v___x_695_ = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(v_a_693_, v_a_691_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref_known(v___x_695_, 1);
if (lean_obj_tag(v_a_696_) == 1)
{
lean_object* v_k_697_; 
v_k_697_ = lean_ctor_get(v_a_696_, 1);
lean_inc_ref(v_k_697_);
if (lean_obj_tag(v_k_697_) == 5)
{
lean_object* v_decl_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_721_; 
v_decl_698_ = lean_ctor_get(v_a_696_, 0);
lean_inc_ref(v_decl_698_);
lean_dec_ref_known(v_a_696_, 2);
v_isSharedCheck_721_ = !lean_is_exclusive(v_k_697_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; 
v_unused_722_ = lean_ctor_get(v_k_697_, 0);
lean_dec(v_unused_722_);
v___x_700_ = v_k_697_;
v_isShared_701_ = v_isSharedCheck_721_;
goto v_resetjp_699_;
}
else
{
lean_dec(v_k_697_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_721_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
uint8_t v___x_702_; lean_object* v___x_703_; 
v___x_702_ = 0;
v___x_703_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v___x_702_, v_decl_698_, v___x_669_, v_a_503_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_params_704_; lean_object* v_value_705_; lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; lean_object* v___x_710_; 
lean_dec_ref_known(v___x_703_, 1);
v_params_704_ = lean_ctor_get(v_decl_698_, 2);
lean_inc_ref(v_params_704_);
v_value_705_ = lean_ctor_get(v_decl_698_, 4);
lean_inc_ref(v_value_705_);
lean_dec_ref(v_decl_698_);
v___x_706_ = l_Lean_ConstantInfo_levelParams(v_val_617_);
lean_dec(v_val_617_);
v___x_707_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_707_, 0, v___y_614_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
lean_ctor_set(v___x_707_, 2, v_a_691_);
lean_ctor_set(v___x_707_, 3, v_params_704_);
v___x_708_ = lean_unbox(v_a_619_);
lean_dec(v_a_619_);
lean_ctor_set_uint8(v___x_707_, sizeof(void*)*4, v___x_708_);
if (v_isShared_701_ == 0)
{
lean_ctor_set_tag(v___x_700_, 0);
lean_ctor_set(v___x_700_, 0, v_value_705_);
v___x_710_ = v___x_700_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_value_705_);
v___x_710_ = v_reuseFailAlloc_712_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_711_; 
v___x_711_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_711_, 0, v___x_707_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
lean_ctor_set(v___x_711_, 2, v___x_622_);
lean_ctor_set_uint8(v___x_711_, sizeof(void*)*3, v___x_669_);
v___y_542_ = v___x_683_;
v___y_543_ = v_env_621_;
v___y_544_ = v___x_669_;
v_decl_545_ = v___x_711_;
v___y_546_ = v_a_502_;
v___y_547_ = v_a_503_;
v___y_548_ = v_a_504_;
v___y_549_ = v_a_505_;
goto v___jp_541_;
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_del_object(v___x_700_);
lean_dec_ref(v_decl_698_);
lean_dec(v_a_691_);
lean_dec(v___x_622_);
lean_dec_ref(v_env_621_);
lean_dec(v_a_619_);
lean_dec(v_val_617_);
lean_dec(v___y_614_);
v_a_713_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_703_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_703_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
else
{
uint8_t v___x_723_; 
lean_dec_ref(v_k_697_);
v___x_723_ = lean_unbox(v_a_619_);
lean_dec(v_a_619_);
v___y_594_ = v___y_614_;
v___y_595_ = v___x_622_;
v___y_596_ = v_a_696_;
v___y_597_ = v___x_683_;
v___y_598_ = v_val_617_;
v___y_599_ = v_env_621_;
v___y_600_ = v___x_723_;
v___y_601_ = v_a_691_;
v___y_602_ = v___x_669_;
v___y_603_ = v_a_502_;
v___y_604_ = v_a_503_;
v___y_605_ = v_a_504_;
v___y_606_ = v_a_505_;
goto v___jp_593_;
}
}
else
{
uint8_t v___x_724_; 
v___x_724_ = lean_unbox(v_a_619_);
lean_dec(v_a_619_);
v___y_594_ = v___y_614_;
v___y_595_ = v___x_622_;
v___y_596_ = v_a_696_;
v___y_597_ = v___x_683_;
v___y_598_ = v_val_617_;
v___y_599_ = v_env_621_;
v___y_600_ = v___x_724_;
v___y_601_ = v_a_691_;
v___y_602_ = v___x_669_;
v___y_603_ = v_a_502_;
v___y_604_ = v_a_503_;
v___y_605_ = v_a_504_;
v___y_606_ = v_a_505_;
goto v___jp_593_;
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec(v_a_691_);
lean_dec(v___x_622_);
lean_dec_ref(v_env_621_);
lean_dec(v_a_619_);
lean_dec(v_val_617_);
lean_dec(v___y_614_);
v_a_725_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_695_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_695_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_dec(v_a_691_);
lean_dec(v___x_689_);
lean_dec(v___x_622_);
lean_dec_ref(v_env_621_);
lean_dec(v_a_619_);
lean_dec(v_val_617_);
lean_dec(v___y_614_);
v_a_733_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_692_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_692_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v___x_689_);
lean_dec_ref_known(v___x_687_, 7);
lean_dec_ref(v___f_675_);
lean_dec(v_val_672_);
lean_dec(v___x_622_);
lean_dec_ref(v_env_621_);
lean_dec(v_a_619_);
lean_dec(v_val_617_);
lean_dec(v___y_614_);
v_a_741_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_690_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_690_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec(v___x_671_);
lean_dec(v___x_622_);
lean_dec_ref(v_env_621_);
lean_dec(v_a_619_);
lean_dec(v_val_617_);
v___x_749_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__20, &l_Lean_Compiler_LCNF_toDecl___closed__20_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__20);
v___x_750_ = l_Lean_MessageData_ofConstName(v___y_614_, v___x_669_);
v___x_751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__22, &l_Lean_Compiler_LCNF_toDecl___closed__22_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__22);
v___x_753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_751_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___x_753_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
return v___x_754_;
}
}
else
{
lean_object* v___x_755_; uint8_t v___x_756_; uint8_t v___x_757_; uint8_t v___x_758_; uint8_t v___x_759_; lean_object* v___x_760_; uint64_t v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
lean_dec_ref(v_env_621_);
v___x_755_ = l_Lean_ConstantInfo_type(v_val_617_);
v___x_756_ = 0;
v___x_757_ = 1;
v___x_758_ = 0;
v___x_759_ = 2;
v___x_760_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_760_, 0, v___x_756_);
lean_ctor_set_uint8(v___x_760_, 1, v___x_756_);
lean_ctor_set_uint8(v___x_760_, 2, v___x_756_);
lean_ctor_set_uint8(v___x_760_, 3, v___x_756_);
lean_ctor_set_uint8(v___x_760_, 4, v___x_756_);
lean_ctor_set_uint8(v___x_760_, 5, v___x_669_);
lean_ctor_set_uint8(v___x_760_, 6, v___x_669_);
lean_ctor_set_uint8(v___x_760_, 7, v___x_756_);
lean_ctor_set_uint8(v___x_760_, 8, v___x_669_);
lean_ctor_set_uint8(v___x_760_, 9, v___x_757_);
lean_ctor_set_uint8(v___x_760_, 10, v___x_758_);
lean_ctor_set_uint8(v___x_760_, 11, v___x_669_);
lean_ctor_set_uint8(v___x_760_, 12, v___x_669_);
lean_ctor_set_uint8(v___x_760_, 13, v___x_669_);
lean_ctor_set_uint8(v___x_760_, 14, v___x_759_);
lean_ctor_set_uint8(v___x_760_, 15, v___x_669_);
lean_ctor_set_uint8(v___x_760_, 16, v___x_669_);
lean_ctor_set_uint8(v___x_760_, 17, v___x_669_);
lean_ctor_set_uint8(v___x_760_, 18, v___x_669_);
lean_ctor_set_uint8(v___x_760_, 19, v___x_756_);
v___x_761_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_760_);
v___x_762_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_762_, 0, v___x_760_);
lean_ctor_set_uint64(v___x_762_, sizeof(void*)*1, v___x_761_);
v___x_763_ = lean_unsigned_to_nat(0u);
v___x_764_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__10, &l_Lean_Compiler_LCNF_toDecl___closed__10_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__10);
v___x_765_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__11));
v___x_766_ = lean_box(0);
v___x_767_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_767_, 0, v___x_762_);
lean_ctor_set(v___x_767_, 1, v___x_612_);
lean_ctor_set(v___x_767_, 2, v___x_764_);
lean_ctor_set(v___x_767_, 3, v___x_765_);
lean_ctor_set(v___x_767_, 4, v___x_766_);
lean_ctor_set(v___x_767_, 5, v___x_763_);
lean_ctor_set(v___x_767_, 6, v___x_766_);
lean_ctor_set_uint8(v___x_767_, sizeof(void*)*7, v___x_756_);
lean_ctor_set_uint8(v___x_767_, sizeof(void*)*7 + 1, v___x_756_);
lean_ctor_set_uint8(v___x_767_, sizeof(void*)*7 + 2, v___x_756_);
lean_ctor_set_uint8(v___x_767_, sizeof(void*)*7 + 3, v___x_670_);
v___x_768_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__18, &l_Lean_Compiler_LCNF_toDecl___closed__18_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__18);
v___x_769_ = lean_st_mk_ref(v___x_768_);
v___x_770_ = l_Lean_Compiler_LCNF_toLCNFType(v___x_755_, v___x_767_, v___x_769_, v_a_504_, v_a_505_);
lean_dec_ref_known(v___x_767_, 7);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc_n(v_a_771_, 2);
lean_dec_ref_known(v___x_770_, 1);
v___x_772_ = lean_st_ref_get(v___x_769_);
lean_dec(v___x_769_);
lean_dec(v___x_772_);
v___x_773_ = l_Lean_Compiler_LCNF_toDecl___lam__0(v_a_771_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_786_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_786_ == 0)
{
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_786_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_786_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_778_ = l_Lean_ConstantInfo_levelParams(v_val_617_);
lean_dec(v_val_617_);
v___x_779_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_779_, 0, v___y_614_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
lean_ctor_set(v___x_779_, 2, v_a_771_);
lean_ctor_set(v___x_779_, 3, v_a_774_);
v___x_780_ = lean_unbox(v_a_619_);
lean_dec(v_a_619_);
lean_ctor_set_uint8(v___x_779_, sizeof(void*)*4, v___x_780_);
v___x_781_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__23));
v___x_782_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_782_, 0, v___x_779_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
lean_ctor_set(v___x_782_, 2, v___x_622_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*3, v___x_756_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_782_);
v___x_784_ = v___x_776_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec(v_a_771_);
lean_dec(v___x_622_);
lean_dec(v_a_619_);
lean_dec(v_val_617_);
lean_dec(v___y_614_);
v_a_787_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_773_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_773_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec(v___x_769_);
lean_dec(v___x_622_);
lean_dec(v_a_619_);
lean_dec(v_val_617_);
lean_dec(v___y_614_);
v_a_795_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_770_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_770_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
}
else
{
lean_object* v___x_803_; uint8_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec(v_a_616_);
v___x_803_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__20, &l_Lean_Compiler_LCNF_toDecl___closed__20_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__20);
v___x_804_ = 0;
v___x_805_ = l_Lean_MessageData_ofConstName(v___y_614_, v___x_804_);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_803_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__25, &l_Lean_Compiler_LCNF_toDecl___closed__25_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__25);
v___x_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___x_808_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
return v___x_809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___boxed(lean_object* v_declName_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_Compiler_LCNF_toDecl(v_declName_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1(uint8_t v___x_819_, lean_object* v_inst_820_, lean_object* v_a_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_819_, v_a_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___boxed(lean_object* v___x_828_, lean_object* v_inst_829_, lean_object* v_a_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
uint8_t v___x_15234__boxed_836_; lean_object* v_res_837_; 
v___x_15234__boxed_836_ = lean_unbox(v___x_828_);
v_res_837_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1(v___x_15234__boxed_836_, v_inst_829_, v_a_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2_spec__2(lean_object* v_00_u03b2_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__14, &l_Lean_Compiler_LCNF_toDecl___closed__14_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__14);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__14, &l_Lean_Compiler_LCNF_toDecl___closed__14_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__14);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___boxed(lean_object* v___dummy_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg();
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Compiler_LCNF_toDecl_spec__2(lean_object* v_00_u03b2_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__14, &l_Lean_Compiler_LCNF_toDecl___closed__14_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__14);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__5(uint8_t v___x_846_, size_t v_sz_847_, size_t v_i_848_, lean_object* v_bs_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v___x_846_, v_sz_847_, v_i_848_, v_bs_849_, v___y_851_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__5___boxed(lean_object* v___x_856_, lean_object* v_sz_857_, lean_object* v_i_858_, lean_object* v_bs_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
uint8_t v___x_15266__boxed_865_; size_t v_sz_boxed_866_; size_t v_i_boxed_867_; lean_object* v_res_868_; 
v___x_15266__boxed_865_ = lean_unbox(v___x_856_);
v_sz_boxed_866_ = lean_unbox_usize(v_sz_857_);
lean_dec(v_sz_857_);
v_i_boxed_867_ = lean_unbox_usize(v_i_858_);
lean_dec(v_i_858_);
v_res_868_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__5(v___x_15266__boxed_865_, v_sz_boxed_866_, v_i_boxed_867_, v_bs_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
return v_res_868_;
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
