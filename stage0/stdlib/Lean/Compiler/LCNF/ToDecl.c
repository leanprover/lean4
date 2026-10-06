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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedBorrowed(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
lean_object* l_Lean_Compiler_mkUnsafeRecName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
uint8_t l_Lean_isExport(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
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
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(uint8_t, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_toDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " Declaration "};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_toDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 321, .m_capacity = 321, .m_length = 320, .m_data = " is marked as `export` but some of its parameters have borrow annotations.\n Consider using `set_option compiler.ignoreBorrowAnnotation true in` to suppress the borrow annotations in its type.\n If the declaration is part of an `export`/`extern` pair make sure to also suppress the annotations at the `extern` declaration."};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__3;
static const lean_ctor_object l_Lean_Compiler_LCNF_toDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_toDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__5_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Compiler_LCNF_toDecl___closed__6;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__7;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__8;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__9;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__10;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__11;
static const lean_array_object l_Lean_Compiler_LCNF_toDecl___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__12_value;
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
static const lean_string_object l_Lean_Compiler_LCNF_toDecl___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declaration `"};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__18 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__18_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__19;
static const lean_string_object l_Lean_Compiler_LCNF_toDecl___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "` does not have a value"};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__20 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__20_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__21;
static const lean_string_object l_Lean_Compiler_LCNF_toDecl___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "` not found"};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__22 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__22_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__23;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_val_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_60_; 
v_val_33_ = lean_ctor_get(v___x_32_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_60_ == 0)
{
v___x_35_ = v___x_32_;
v_isShared_36_ = v_isSharedCheck_60_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_val_33_);
lean_dec(v___x_32_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_60_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
uint8_t v___x_37_; uint8_t v___y_39_; 
v___x_37_ = l_Lean_ConstantInfo_isUnsafe(v_val_33_);
if (v___x_37_ == 0)
{
uint8_t v___x_55_; 
v___x_55_ = 1;
if (lean_obj_tag(v_val_33_) == 3)
{
lean_dec_ref_known(v_val_33_, 1);
v___y_39_ = v___x_55_;
goto v___jp_38_;
}
else
{
lean_dec(v_val_33_);
if (v___x_37_ == 0)
{
lean_object* v___x_56_; lean_object* v___x_57_; 
lean_del_object(v___x_35_);
lean_dec_ref(v_env_30_);
lean_dec(v_declName_26_);
v___x_56_ = lean_box(v___x_55_);
v___x_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
return v___x_57_;
}
else
{
v___y_39_ = v___x_37_;
goto v___jp_38_;
}
}
}
else
{
lean_object* v___x_58_; lean_object* v___x_59_; 
lean_del_object(v___x_35_);
lean_dec(v_val_33_);
lean_dec_ref(v_env_30_);
lean_dec(v_declName_26_);
v___x_58_ = lean_box(v___x_31_);
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
v___jp_38_:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = l_Lean_Compiler_mkUnsafeRecName(v_declName_26_);
v___x_41_ = l_Lean_Environment_find_x3f(v_env_30_, v___x_40_, v___x_37_);
if (lean_obj_tag(v___x_41_) == 0)
{
lean_object* v___x_42_; lean_object* v___x_44_; 
v___x_42_ = lean_box(v___y_39_);
if (v_isShared_36_ == 0)
{
lean_ctor_set_tag(v___x_35_, 0);
lean_ctor_set(v___x_35_, 0, v___x_42_);
v___x_44_ = v___x_35_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v___x_42_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
else
{
lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_53_; 
lean_del_object(v___x_35_);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_53_ == 0)
{
lean_object* v_unused_54_; 
v_unused_54_ = lean_ctor_get(v___x_41_, 0);
lean_dec(v_unused_54_);
v___x_47_ = v___x_41_;
v_isShared_48_ = v_isSharedCheck_53_;
goto v_resetjp_46_;
}
else
{
lean_dec(v___x_41_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_53_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_49_; lean_object* v___x_51_; 
v___x_49_ = lean_box(v___x_37_);
if (v_isShared_48_ == 0)
{
lean_ctor_set_tag(v___x_47_, 0);
lean_ctor_set(v___x_47_, 0, v___x_49_);
v___x_51_ = v___x_47_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v___x_49_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
return v___x_51_;
}
}
}
}
}
}
else
{
uint8_t v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec(v___x_32_);
lean_dec_ref(v_env_30_);
lean_dec(v_declName_26_);
v___x_61_ = 1;
v___x_62_ = lean_box(v___x_61_);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg___boxed(lean_object* v_declName_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(v_declName_64_, v_a_65_);
lean_dec(v_a_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe(lean_object* v_declName_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(v_declName_68_, v_a_70_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe___boxed(lean_object* v_declName_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Compiler_LCNF_declIsNotUnsafe(v_declName_73_, v_a_74_, v_a_75_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
return v_res_77_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(lean_object* v_opts_78_, lean_object* v_opt_79_){
_start:
{
lean_object* v_name_80_; lean_object* v_defValue_81_; lean_object* v_map_82_; lean_object* v___x_83_; 
v_name_80_ = lean_ctor_get(v_opt_79_, 0);
v_defValue_81_ = lean_ctor_get(v_opt_79_, 1);
v_map_82_ = lean_ctor_get(v_opts_78_, 0);
v___x_83_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_82_, v_name_80_);
if (lean_obj_tag(v___x_83_) == 0)
{
uint8_t v___x_84_; 
v___x_84_ = lean_unbox(v_defValue_81_);
return v___x_84_;
}
else
{
lean_object* v_val_85_; 
v_val_85_ = lean_ctor_get(v___x_83_, 0);
lean_inc(v_val_85_);
lean_dec_ref_known(v___x_83_, 1);
if (lean_obj_tag(v_val_85_) == 1)
{
uint8_t v_v_86_; 
v_v_86_ = lean_ctor_get_uint8(v_val_85_, 0);
lean_dec_ref_known(v_val_85_, 0);
return v_v_86_;
}
else
{
uint8_t v___x_87_; 
lean_dec(v_val_85_);
v___x_87_ = lean_unbox(v_defValue_81_);
return v___x_87_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0___boxed(lean_object* v_opts_88_, lean_object* v_opt_89_){
_start:
{
uint8_t v_res_90_; lean_object* v_r_91_; 
v_res_90_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(v_opts_88_, v_opt_89_);
lean_dec_ref(v_opt_89_);
lean_dec_ref(v_opts_88_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_92_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_95_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_96_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__1);
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
lean_ctor_set(v___x_98_, 2, v___x_97_);
lean_ctor_set(v___x_98_, 3, v___x_97_);
lean_ctor_set(v___x_98_, 4, v___x_96_);
lean_ctor_set(v___x_98_, 5, v___x_96_);
lean_ctor_set(v___x_98_, 6, v___x_96_);
lean_ctor_set(v___x_98_, 7, v___x_96_);
lean_ctor_set(v___x_98_, 8, v___x_96_);
lean_ctor_set(v___x_98_, 9, v___x_96_);
lean_ctor_set(v___x_98_, 10, v___x_96_);
lean_ctor_set(v___x_98_, 11, v___x_95_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(lean_object* v_msg_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_ref_105_; lean_object* v___x_106_; lean_object* v_env_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_ref_105_ = lean_ctor_get(v___y_102_, 2);
v___x_106_ = lean_st_ref_get(v___y_103_);
v_env_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc_ref(v_env_107_);
lean_dec(v___x_106_);
v___x_108_ = lean_st_ref_get(v___y_101_);
v___x_109_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_100_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_132_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_132_ == 0)
{
v___x_112_ = v___x_109_;
v_isShared_113_ = v_isSharedCheck_132_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_132_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v_lctx_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_130_; 
v_lctx_114_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_130_ == 0)
{
lean_object* v_unused_131_; 
v_unused_131_ = lean_ctor_get(v___x_108_, 1);
lean_dec(v_unused_131_);
v___x_116_ = v___x_108_;
v_isShared_117_ = v_isSharedCheck_130_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_lctx_114_);
lean_dec(v___x_108_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_130_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
uint8_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_118_ = lean_unbox(v_a_110_);
lean_dec(v_a_110_);
v___x_119_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_114_, v___x_118_);
lean_dec_ref(v_lctx_114_);
v___x_120_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_102_);
v___x_121_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__2, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__2_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__2);
v___x_122_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_122_, 0, v_env_107_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
lean_ctor_set(v___x_122_, 2, v___x_119_);
lean_ctor_set(v___x_122_, 3, v___x_120_);
if (v_isShared_117_ == 0)
{
lean_ctor_set_tag(v___x_116_, 3);
lean_ctor_set(v___x_116_, 1, v_msg_99_);
lean_ctor_set(v___x_116_, 0, v___x_122_);
v___x_124_ = v___x_116_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_msg_99_);
v___x_124_ = v_reuseFailAlloc_129_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
lean_inc(v_ref_105_);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v_ref_105_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
if (v_isShared_113_ == 0)
{
lean_ctor_set_tag(v___x_112_, 1);
lean_ctor_set(v___x_112_, 0, v___x_125_);
v___x_127_ = v___x_112_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
}
else
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_140_; 
lean_dec(v___x_108_);
lean_dec_ref(v_env_107_);
lean_dec_ref(v_msg_99_);
v_a_133_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_140_ == 0)
{
v___x_135_ = v___x_109_;
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_109_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_138_; 
if (v_isShared_136_ == 0)
{
v___x_138_ = v___x_135_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_a_133_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___boxed(lean_object* v_msg_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v_msg_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2(lean_object* v_00_u03b1_148_, lean_object* v_msg_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v_msg_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___boxed(lean_object* v_00_u03b1_156_, lean_object* v_msg_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2(v_00_u03b1_156_, v_msg_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0(lean_object* v_k_164_, lean_object* v_b_165_, lean_object* v_c_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v___x_172_; 
lean_inc(v___y_170_);
lean_inc_ref(v___y_169_);
lean_inc(v___y_168_);
lean_inc_ref(v___y_167_);
v___x_172_ = lean_apply_7(v_k_164_, v_b_165_, v_c_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, lean_box(0));
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0___boxed(lean_object* v_k_173_, lean_object* v_b_174_, lean_object* v_c_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0(v_k_173_, v_b_174_, v_c_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(lean_object* v_e_182_, lean_object* v_k_183_, uint8_t v_cleanupAnnotations_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___f_190_; uint8_t v___x_191_; uint8_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___f_190_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_190_, 0, v_k_183_);
v___x_191_ = 1;
v___x_192_ = 0;
v___x_193_ = lean_box(0);
v___x_194_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_182_, v___x_191_, v___x_192_, v___x_191_, v___x_192_, v___x_193_, v___f_190_, v_cleanupAnnotations_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
v_a_203_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_194_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_194_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___boxed(lean_object* v_e_211_, lean_object* v_k_212_, lean_object* v_cleanupAnnotations_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_219_; lean_object* v_res_220_; 
v_cleanupAnnotations_boxed_219_ = lean_unbox(v_cleanupAnnotations_213_);
v_res_220_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v_e_211_, v_k_212_, v_cleanupAnnotations_boxed_219_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5(lean_object* v_00_u03b1_221_, lean_object* v_e_222_, lean_object* v_k_223_, uint8_t v_cleanupAnnotations_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v_e_222_, v_k_223_, v_cleanupAnnotations_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___boxed(lean_object* v_00_u03b1_231_, lean_object* v_e_232_, lean_object* v_k_233_, lean_object* v_cleanupAnnotations_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_240_; lean_object* v_res_241_; 
v_cleanupAnnotations_boxed_240_ = lean_unbox(v_cleanupAnnotations_234_);
v_res_241_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5(v_00_u03b1_231_, v_e_232_, v_k_233_, v_cleanupAnnotations_boxed_240_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(uint8_t v___x_242_, lean_object* v_a_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_snd_249_; 
v_snd_249_ = lean_ctor_get(v_a_243_, 1);
lean_inc(v_snd_249_);
if (lean_obj_tag(v_snd_249_) == 7)
{
lean_object* v_fst_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_277_; 
v_fst_250_ = lean_ctor_get(v_a_243_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v_a_243_);
if (v_isSharedCheck_277_ == 0)
{
lean_object* v_unused_278_; 
v_unused_278_ = lean_ctor_get(v_a_243_, 1);
lean_dec(v_unused_278_);
v___x_252_ = v_a_243_;
v_isShared_253_ = v_isSharedCheck_277_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_fst_250_);
lean_dec(v_a_243_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_277_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v_binderName_254_; lean_object* v_binderType_255_; lean_object* v_body_256_; uint8_t v___y_258_; 
v_binderName_254_ = lean_ctor_get(v_snd_249_, 0);
lean_inc(v_binderName_254_);
v_binderType_255_ = lean_ctor_get(v_snd_249_, 1);
lean_inc_ref(v_binderType_255_);
v_body_256_ = lean_ctor_get(v_snd_249_, 2);
lean_inc_ref(v_body_256_);
lean_dec_ref_known(v_snd_249_, 3);
if (v___x_242_ == 0)
{
uint8_t v___x_275_; 
v___x_275_ = l_Lean_isMarkedBorrowed(v_binderType_255_);
v___y_258_ = v___x_275_;
goto v___jp_257_;
}
else
{
uint8_t v___x_276_; 
v___x_276_ = 0;
v___y_258_ = v___x_276_;
goto v___jp_257_;
}
v___jp_257_:
{
uint8_t v___x_259_; lean_object* v___x_260_; 
v___x_259_ = 0;
v___x_260_ = l_Lean_Compiler_LCNF_mkParam(v___x_259_, v_binderName_254_, v_binderType_255_, v___y_258_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v___x_260_, 1);
v___x_262_ = lean_array_push(v_fst_250_, v_a_261_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 1, v_body_256_);
lean_ctor_set(v___x_252_, 0, v___x_262_);
v___x_264_ = v___x_252_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_body_256_);
v___x_264_ = v_reuseFailAlloc_266_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
v_a_243_ = v___x_264_;
goto _start;
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
lean_dec_ref(v_body_256_);
lean_del_object(v___x_252_);
lean_dec(v_fst_250_);
v_a_267_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_260_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_260_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
}
else
{
lean_object* v_fst_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_287_; 
v_fst_279_ = lean_ctor_get(v_a_243_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v_a_243_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; 
v_unused_288_ = lean_ctor_get(v_a_243_, 1);
lean_dec(v_unused_288_);
v___x_281_ = v_a_243_;
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_fst_279_);
lean_dec(v_a_243_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_fst_279_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_snd_249_);
v___x_284_ = v_reuseFailAlloc_286_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_285_; 
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg___boxed(lean_object* v___x_289_, lean_object* v_a_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
uint8_t v___x_13578__boxed_296_; lean_object* v_res_297_; 
v___x_13578__boxed_296_ = lean_unbox(v___x_289_);
v_res_297_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_13578__boxed_296_, v_a_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0(lean_object* v_expr_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_306_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0));
v___x_307_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_303_);
v___x_308_ = l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
v___x_309_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(v___x_307_, v___x_308_);
lean_dec_ref(v___x_307_);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_306_);
lean_ctor_set(v___x_310_, 1, v_expr_300_);
v___x_311_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_309_, v___x_310_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_320_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_320_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_320_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_320_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v_fst_316_; lean_object* v___x_318_; 
v_fst_316_ = lean_ctor_get(v_a_312_, 0);
lean_inc(v_fst_316_);
lean_dec(v_a_312_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v_fst_316_);
v___x_318_ = v___x_314_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_fst_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
v_a_321_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___x_311_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_311_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0___boxed(lean_object* v_expr_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_Compiler_LCNF_toDecl___lam__0(v_expr_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1(uint8_t v___x_336_, uint8_t v___x_337_, lean_object* v_xs_338_, lean_object* v_body_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_Meta_etaExpand(v_body_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; uint8_t v___x_347_; lean_object* v___x_348_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref_known(v___x_345_, 1);
v___x_347_ = 1;
v___x_348_ = l_Lean_Meta_mkLambdaFVars(v_xs_338_, v_a_346_, v___x_336_, v___x_337_, v___x_336_, v___x_337_, v___x_347_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
return v___x_348_;
}
else
{
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1___boxed(lean_object* v___x_349_, lean_object* v___x_350_, lean_object* v_xs_351_, lean_object* v_body_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
uint8_t v___x_13736__boxed_358_; uint8_t v___x_13737__boxed_359_; lean_object* v_res_360_; 
v___x_13736__boxed_358_ = lean_unbox(v___x_349_);
v___x_13737__boxed_359_ = lean_unbox(v___x_350_);
v_res_360_ = l_Lean_Compiler_LCNF_toDecl___lam__1(v___x_13736__boxed_358_, v___x_13737__boxed_359_, v_xs_351_, v_body_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec_ref(v_xs_351_);
return v_res_360_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(lean_object* v_as_361_, size_t v_i_362_, size_t v_stop_363_){
_start:
{
uint8_t v___x_364_; 
v___x_364_ = lean_usize_dec_eq(v_i_362_, v_stop_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; uint8_t v_borrow_366_; 
v___x_365_ = lean_array_uget_borrowed(v_as_361_, v_i_362_);
v_borrow_366_ = lean_ctor_get_uint8(v___x_365_, sizeof(void*)*3);
if (v_borrow_366_ == 0)
{
size_t v___x_367_; size_t v___x_368_; 
v___x_367_ = ((size_t)1ULL);
v___x_368_ = lean_usize_add(v_i_362_, v___x_367_);
v_i_362_ = v___x_368_;
goto _start;
}
else
{
return v_borrow_366_;
}
}
else
{
uint8_t v___x_370_; 
v___x_370_ = 0;
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3___boxed(lean_object* v_as_371_, lean_object* v_i_372_, lean_object* v_stop_373_){
_start:
{
size_t v_i_boxed_374_; size_t v_stop_boxed_375_; uint8_t v_res_376_; lean_object* v_r_377_; 
v_i_boxed_374_ = lean_unbox_usize(v_i_372_);
lean_dec(v_i_372_);
v_stop_boxed_375_ = lean_unbox_usize(v_stop_373_);
lean_dec(v_stop_373_);
v_res_376_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(v_as_371_, v_i_boxed_374_, v_stop_boxed_375_);
lean_dec_ref(v_as_371_);
v_r_377_ = lean_box(v_res_376_);
return v_r_377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(uint8_t v___x_378_, size_t v_sz_379_, size_t v_i_380_, lean_object* v_bs_381_, lean_object* v___y_382_){
_start:
{
uint8_t v___x_384_; 
v___x_384_ = lean_usize_dec_lt(v_i_380_, v_sz_379_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; 
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v_bs_381_);
return v___x_385_;
}
else
{
lean_object* v_v_386_; lean_object* v___x_387_; lean_object* v_bs_x27_388_; uint8_t v___x_389_; lean_object* v___x_390_; 
v_v_386_ = lean_array_uget(v_bs_381_, v_i_380_);
v___x_387_ = lean_unsigned_to_nat(0u);
v_bs_x27_388_ = lean_array_uset(v_bs_381_, v_i_380_, v___x_387_);
v___x_389_ = 0;
v___x_390_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v___x_389_, v_v_386_, v___x_378_, v___y_382_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; size_t v___x_392_; size_t v___x_393_; lean_object* v___x_394_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
lean_dec_ref_known(v___x_390_, 1);
v___x_392_ = ((size_t)1ULL);
v___x_393_ = lean_usize_add(v_i_380_, v___x_392_);
v___x_394_ = lean_array_uset(v_bs_x27_388_, v_i_380_, v_a_391_);
v_i_380_ = v___x_393_;
v_bs_381_ = v___x_394_;
goto _start;
}
else
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
lean_dec_ref(v_bs_x27_388_);
v_a_396_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_403_ == 0)
{
v___x_398_ = v___x_390_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_390_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_396_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___boxed(lean_object* v___x_404_, lean_object* v_sz_405_, lean_object* v_i_406_, lean_object* v_bs_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
uint8_t v___x_13778__boxed_410_; size_t v_sz_boxed_411_; size_t v_i_boxed_412_; lean_object* v_res_413_; 
v___x_13778__boxed_410_ = lean_unbox(v___x_404_);
v_sz_boxed_411_ = lean_unbox_usize(v_sz_405_);
lean_dec(v_sz_405_);
v_i_boxed_412_ = lean_unbox_usize(v_i_406_);
lean_dec(v_i_406_);
v_res_413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___x_13778__boxed_410_, v_sz_boxed_411_, v_i_boxed_412_, v_bs_407_, v___y_408_);
lean_dec(v___y_408_);
return v_res_413_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__1(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__0));
v___x_416_ = l_Lean_stringToMessageData(v___x_415_);
return v___x_416_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__3(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__2));
v___x_419_ = l_Lean_stringToMessageData(v___x_418_);
return v___x_419_;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_toDecl___closed__6(void){
_start:
{
lean_object* v___x_428_; uint64_t v___x_429_; 
v___x_428_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__5));
v___x_429_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_428_);
return v___x_429_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__7(void){
_start:
{
uint64_t v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_430_ = lean_uint64_once(&l_Lean_Compiler_LCNF_toDecl___closed__6, &l_Lean_Compiler_LCNF_toDecl___closed__6_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__6);
v___x_431_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__5));
v___x_432_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set_uint64(v___x_432_, sizeof(void*)*1, v___x_430_);
return v___x_432_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__8(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__9(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = lean_unsigned_to_nat(32u);
v___x_436_ = lean_mk_empty_array_with_capacity(v___x_435_);
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__10(void){
_start:
{
size_t v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_438_ = ((size_t)5ULL);
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = lean_unsigned_to_nat(32u);
v___x_441_ = lean_mk_empty_array_with_capacity(v___x_440_);
v___x_442_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__9, &l_Lean_Compiler_LCNF_toDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__9);
v___x_443_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_443_, 0, v___x_442_);
lean_ctor_set(v___x_443_, 1, v___x_441_);
lean_ctor_set(v___x_443_, 2, v___x_439_);
lean_ctor_set(v___x_443_, 3, v___x_439_);
lean_ctor_set_usize(v___x_443_, 4, v___x_438_);
return v___x_443_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__11(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_444_ = lean_box(1);
v___x_445_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__10, &l_Lean_Compiler_LCNF_toDecl___closed__10_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__10);
v___x_446_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__8, &l_Lean_Compiler_LCNF_toDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__8);
v___x_447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v___x_445_);
lean_ctor_set(v___x_447_, 2, v___x_444_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__13(void){
_start:
{
uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_450_ = 1;
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = lean_box(0);
v___x_453_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__12));
v___x_454_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__11, &l_Lean_Compiler_LCNF_toDecl___closed__11_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__11);
v___x_455_ = lean_box(1);
v___x_456_ = 0;
v___x_457_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__7, &l_Lean_Compiler_LCNF_toDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__7);
v___x_458_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___x_455_);
lean_ctor_set(v___x_458_, 2, v___x_454_);
lean_ctor_set(v___x_458_, 3, v___x_453_);
lean_ctor_set(v___x_458_, 4, v___x_452_);
lean_ctor_set(v___x_458_, 5, v___x_451_);
lean_ctor_set(v___x_458_, 6, v___x_452_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*7, v___x_456_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*7 + 1, v___x_456_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*7 + 2, v___x_456_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*7 + 3, v___x_450_);
return v___x_458_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__14(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_459_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_460_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__8, &l_Lean_Compiler_LCNF_toDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__8);
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
lean_ctor_set(v___x_462_, 2, v___x_461_);
lean_ctor_set(v___x_462_, 3, v___x_461_);
lean_ctor_set(v___x_462_, 4, v___x_460_);
lean_ctor_set(v___x_462_, 5, v___x_460_);
lean_ctor_set(v___x_462_, 6, v___x_460_);
lean_ctor_set(v___x_462_, 7, v___x_460_);
lean_ctor_set(v___x_462_, 8, v___x_460_);
lean_ctor_set(v___x_462_, 9, v___x_460_);
lean_ctor_set(v___x_462_, 10, v___x_460_);
lean_ctor_set(v___x_462_, 11, v___x_459_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__15(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__8, &l_Lean_Compiler_LCNF_toDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__8);
v___x_464_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
lean_ctor_set(v___x_464_, 2, v___x_463_);
lean_ctor_set(v___x_464_, 3, v___x_463_);
lean_ctor_set(v___x_464_, 4, v___x_463_);
lean_ctor_set(v___x_464_, 5, v___x_463_);
return v___x_464_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__16(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__8, &l_Lean_Compiler_LCNF_toDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__8);
v___x_466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
lean_ctor_set(v___x_466_, 2, v___x_465_);
lean_ctor_set(v___x_466_, 3, v___x_465_);
lean_ctor_set(v___x_466_, 4, v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__17(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_467_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__16, &l_Lean_Compiler_LCNF_toDecl___closed__16_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__16);
v___x_468_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__10, &l_Lean_Compiler_LCNF_toDecl___closed__10_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__10);
v___x_469_ = lean_box(1);
v___x_470_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__15, &l_Lean_Compiler_LCNF_toDecl___closed__15_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__15);
v___x_471_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__14, &l_Lean_Compiler_LCNF_toDecl___closed__14_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__14);
v___x_472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v___x_470_);
lean_ctor_set(v___x_472_, 2, v___x_469_);
lean_ctor_set(v___x_472_, 3, v___x_468_);
lean_ctor_set(v___x_472_, 4, v___x_467_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__19(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__18));
v___x_475_ = l_Lean_stringToMessageData(v___x_474_);
return v___x_475_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__21(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__20));
v___x_478_ = l_Lean_stringToMessageData(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__23(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__22));
v___x_481_ = l_Lean_stringToMessageData(v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object* v_declName_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; uint8_t v___y_495_; lean_object* v___y_512_; lean_object* v___y_513_; uint8_t v___y_514_; lean_object* v_decl_515_; lean_object* v_name_516_; lean_object* v_params_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_531_; lean_object* v___y_532_; uint8_t v___y_533_; lean_object* v_decl_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_583_; uint8_t v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; uint8_t v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_602_; lean_object* v___y_603_; uint8_t v___y_604_; lean_object* v___y_605_; uint8_t v___y_606_; lean_object* v___y_607_; lean_object* v_a_608_; lean_object* v___y_631_; uint8_t v___y_632_; lean_object* v___y_633_; uint8_t v___y_634_; lean_object* v___y_635_; lean_object* v_a_636_; lean_object* v___x_658_; lean_object* v___y_660_; lean_object* v___x_812_; 
v___x_658_ = lean_box(1);
v___x_812_ = l_Lean_Compiler_isUnsafeRecName_x3f(v_declName_482_);
if (lean_obj_tag(v___x_812_) == 1)
{
lean_object* v_val_813_; 
lean_dec(v_declName_482_);
v_val_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_val_813_);
lean_dec_ref_known(v___x_812_, 1);
v___y_660_ = v_val_813_;
goto v___jp_659_;
}
else
{
lean_dec(v___x_812_);
v___y_660_ = v_declName_482_;
goto v___jp_659_;
}
v___jp_488_:
{
if (v___y_495_ == 0)
{
lean_object* v___x_496_; 
lean_dec(v___y_489_);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___y_490_);
return v___x_496_;
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
lean_dec_ref(v___y_490_);
v___x_497_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__1, &l_Lean_Compiler_LCNF_toDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__1);
v___x_498_ = l_Lean_MessageData_ofName(v___y_489_);
v___x_499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__3, &l_Lean_Compiler_LCNF_toDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__3);
v___x_501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v___x_501_, v___y_494_, v___y_492_, v___y_491_, v___y_493_);
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
v___jp_511_:
{
uint8_t v___x_522_; 
lean_inc(v_name_516_);
v___x_522_ = l_Lean_isExport(v___y_513_, v_name_516_);
if (v___x_522_ == 0)
{
lean_dec_ref(v_params_517_);
v___y_489_ = v_name_516_;
v___y_490_ = v_decl_515_;
v___y_491_ = v___y_520_;
v___y_492_ = v___y_519_;
v___y_493_ = v___y_521_;
v___y_494_ = v___y_518_;
v___y_495_ = v___y_514_;
goto v___jp_488_;
}
else
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = lean_array_get_size(v_params_517_);
v___x_524_ = lean_nat_dec_lt(v___y_512_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
lean_dec_ref(v_params_517_);
lean_dec(v_name_516_);
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v_decl_515_);
return v___x_525_;
}
else
{
if (v___x_524_ == 0)
{
lean_object* v___x_526_; 
lean_dec_ref(v_params_517_);
lean_dec(v_name_516_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v_decl_515_);
return v___x_526_;
}
else
{
size_t v___x_527_; size_t v___x_528_; uint8_t v___x_529_; 
v___x_527_ = ((size_t)0ULL);
v___x_528_ = lean_usize_of_nat(v___x_523_);
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(v_params_517_, v___x_527_, v___x_528_);
lean_dec_ref(v_params_517_);
v___y_489_ = v_name_516_;
v___y_490_ = v_decl_515_;
v___y_491_ = v___y_520_;
v___y_492_ = v___y_519_;
v___y_493_ = v___y_521_;
v___y_494_ = v___y_518_;
v___y_495_ = v___x_529_;
goto v___jp_488_;
}
}
}
}
v___jp_530_:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_Compiler_LCNF_Decl_etaExpand(v_decl_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref_known(v___x_539_, 1);
v___x_541_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_537_);
v___x_542_ = l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
v___x_543_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(v___x_541_, v___x_542_);
lean_dec_ref(v___x_541_);
if (v___x_543_ == 0)
{
lean_object* v_toSignature_544_; lean_object* v_name_545_; lean_object* v_params_546_; 
v_toSignature_544_ = lean_ctor_get(v_a_540_, 0);
v_name_545_ = lean_ctor_get(v_toSignature_544_, 0);
lean_inc(v_name_545_);
v_params_546_ = lean_ctor_get(v_toSignature_544_, 3);
lean_inc_ref(v_params_546_);
v___y_512_ = v___y_532_;
v___y_513_ = v___y_531_;
v___y_514_ = v___y_533_;
v_decl_515_ = v_a_540_;
v_name_516_ = v_name_545_;
v_params_517_ = v_params_546_;
v___y_518_ = v___y_535_;
v___y_519_ = v___y_536_;
v___y_520_ = v___y_537_;
v___y_521_ = v___y_538_;
goto v___jp_511_;
}
else
{
lean_object* v_toSignature_547_; lean_object* v_value_548_; uint8_t v_recursive_549_; lean_object* v_inlineAttr_x3f_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_581_; 
v_toSignature_547_ = lean_ctor_get(v_a_540_, 0);
v_value_548_ = lean_ctor_get(v_a_540_, 1);
v_recursive_549_ = lean_ctor_get_uint8(v_a_540_, sizeof(void*)*3);
v_inlineAttr_x3f_550_ = lean_ctor_get(v_a_540_, 2);
v_isSharedCheck_581_ = !lean_is_exclusive(v_a_540_);
if (v_isSharedCheck_581_ == 0)
{
v___x_552_ = v_a_540_;
v_isShared_553_ = v_isSharedCheck_581_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_inlineAttr_x3f_550_);
lean_inc(v_value_548_);
lean_inc(v_toSignature_547_);
lean_dec(v_a_540_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_581_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v_name_554_; lean_object* v_levelParams_555_; lean_object* v_type_556_; lean_object* v_params_557_; uint8_t v_safe_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_580_; 
v_name_554_ = lean_ctor_get(v_toSignature_547_, 0);
v_levelParams_555_ = lean_ctor_get(v_toSignature_547_, 1);
v_type_556_ = lean_ctor_get(v_toSignature_547_, 2);
v_params_557_ = lean_ctor_get(v_toSignature_547_, 3);
v_safe_558_ = lean_ctor_get_uint8(v_toSignature_547_, sizeof(void*)*4);
v_isSharedCheck_580_ = !lean_is_exclusive(v_toSignature_547_);
if (v_isSharedCheck_580_ == 0)
{
v___x_560_ = v_toSignature_547_;
v_isShared_561_ = v_isSharedCheck_580_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_params_557_);
lean_inc(v_type_556_);
lean_inc(v_levelParams_555_);
lean_inc(v_name_554_);
lean_dec(v_toSignature_547_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_580_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
size_t v_sz_562_; size_t v___x_563_; lean_object* v___x_564_; 
v_sz_562_ = lean_array_size(v_params_557_);
v___x_563_ = ((size_t)0ULL);
v___x_564_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___y_533_, v_sz_562_, v___x_563_, v_params_557_, v___y_536_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc_n(v_a_565_, 2);
lean_dec_ref_known(v___x_564_, 1);
lean_inc(v_name_554_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 3, v_a_565_);
v___x_567_ = v___x_560_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_name_554_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_levelParams_555_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v_type_556_);
lean_ctor_set(v_reuseFailAlloc_571_, 3, v_a_565_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, sizeof(void*)*4, v_safe_558_);
v___x_567_ = v_reuseFailAlloc_571_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_569_; 
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_567_);
v___x_569_ = v___x_552_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_value_548_);
lean_ctor_set(v_reuseFailAlloc_570_, 2, v_inlineAttr_x3f_550_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, sizeof(void*)*3, v_recursive_549_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
v___y_512_ = v___y_532_;
v___y_513_ = v___y_531_;
v___y_514_ = v___y_533_;
v_decl_515_ = v___x_569_;
v_name_516_ = v_name_554_;
v_params_517_ = v_a_565_;
v___y_518_ = v___y_535_;
v___y_519_ = v___y_536_;
v___y_520_ = v___y_537_;
v___y_521_ = v___y_538_;
goto v___jp_511_;
}
}
}
else
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
lean_del_object(v___x_560_);
lean_dec_ref(v_type_556_);
lean_dec(v_levelParams_555_);
lean_dec(v_name_554_);
lean_del_object(v___x_552_);
lean_dec(v_inlineAttr_x3f_550_);
lean_dec_ref(v_value_548_);
lean_dec_ref(v___y_531_);
v_a_572_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___x_564_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_564_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_531_);
return v___x_539_;
}
}
v___jp_582_:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_596_ = l_Lean_ConstantInfo_levelParams(v___y_585_);
lean_dec_ref(v___y_585_);
v___x_597_ = lean_mk_empty_array_with_capacity(v___y_587_);
v___x_598_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_598_, 0, v___y_583_);
lean_ctor_set(v___x_598_, 1, v___x_596_);
lean_ctor_set(v___x_598_, 2, v___y_590_);
lean_ctor_set(v___x_598_, 3, v___x_597_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*4, v___y_584_);
v___x_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_599_, 0, v___y_589_);
v___x_600_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
lean_ctor_set(v___x_600_, 2, v___y_591_);
lean_ctor_set_uint8(v___x_600_, sizeof(void*)*3, v___y_588_);
v___y_531_ = v___y_586_;
v___y_532_ = v___y_587_;
v___y_533_ = v___y_588_;
v_decl_534_ = v___x_600_;
v___y_535_ = v___y_592_;
v___y_536_ = v___y_593_;
v___y_537_ = v___y_594_;
v___y_538_ = v___y_595_;
goto v___jp_530_;
}
v___jp_601_:
{
lean_object* v___x_609_; 
lean_inc_ref(v_a_608_);
v___x_609_ = l_Lean_Compiler_LCNF_toDecl___lam__0(v_a_608_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_621_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_621_ == 0)
{
v___x_612_ = v___x_609_;
v_isShared_613_ = v_isSharedCheck_621_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_609_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_621_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_614_ = l_Lean_ConstantInfo_levelParams(v___y_605_);
lean_dec_ref(v___y_605_);
v___x_615_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_615_, 0, v___y_603_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
lean_ctor_set(v___x_615_, 2, v_a_608_);
lean_ctor_set(v___x_615_, 3, v_a_610_);
lean_ctor_set_uint8(v___x_615_, sizeof(void*)*4, v___y_604_);
v___x_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_616_, 0, v___y_602_);
v___x_617_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
lean_ctor_set(v___x_617_, 2, v___y_607_);
lean_ctor_set_uint8(v___x_617_, sizeof(void*)*3, v___y_606_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_617_);
v___x_619_ = v___x_612_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec_ref(v_a_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_603_);
lean_dec(v___y_602_);
v_a_622_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_609_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_609_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
v___jp_630_:
{
lean_object* v___x_637_; 
lean_inc_ref(v_a_636_);
v___x_637_ = l_Lean_Compiler_LCNF_toDecl___lam__0(v_a_636_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_649_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_649_ == 0)
{
v___x_640_ = v___x_637_;
v_isShared_641_ = v_isSharedCheck_649_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_637_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_649_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_642_ = l_Lean_ConstantInfo_levelParams(v___y_633_);
lean_dec_ref(v___y_633_);
v___x_643_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_643_, 0, v___y_631_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
lean_ctor_set(v___x_643_, 2, v_a_636_);
lean_ctor_set(v___x_643_, 3, v_a_638_);
lean_ctor_set_uint8(v___x_643_, sizeof(void*)*4, v___y_632_);
v___x_644_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__4));
v___x_645_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_645_, 0, v___x_643_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
lean_ctor_set(v___x_645_, 2, v___y_635_);
lean_ctor_set_uint8(v___x_645_, sizeof(void*)*3, v___y_634_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_645_);
v___x_647_ = v___x_640_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec_ref(v_a_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_631_);
v_a_650_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_637_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_637_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
v___jp_659_:
{
lean_object* v___x_661_; lean_object* v_a_662_; 
lean_inc(v___y_660_);
v___x_661_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(v___y_660_, v_a_486_);
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref(v___x_661_);
if (lean_obj_tag(v_a_662_) == 1)
{
lean_object* v_val_663_; lean_object* v___x_664_; lean_object* v_a_665_; lean_object* v___x_666_; lean_object* v_env_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v_val_663_ = lean_ctor_get(v_a_662_, 0);
lean_inc(v_val_663_);
lean_dec_ref_known(v_a_662_, 1);
lean_inc_n(v___y_660_, 3);
v___x_664_ = l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(v___y_660_, v_a_486_);
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref(v___x_664_);
v___x_666_ = lean_st_ref_get(v_a_486_);
v_env_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc_ref_n(v_env_667_, 3);
lean_dec(v___x_666_);
v___x_668_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_667_, v___y_660_);
v___x_669_ = l_Lean_getExternAttrData_x3f(v_env_667_, v___y_660_);
if (lean_obj_tag(v___x_669_) == 1)
{
lean_object* v_val_670_; lean_object* v___x_671_; uint8_t v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec_ref(v_env_667_);
v_val_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_val_670_);
lean_dec_ref_known(v___x_669_, 1);
v___x_671_ = l_Lean_ConstantInfo_type(v_val_663_);
v___x_672_ = 0;
v___x_673_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__13, &l_Lean_Compiler_LCNF_toDecl___closed__13_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__13);
v___x_674_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__17, &l_Lean_Compiler_LCNF_toDecl___closed__17_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__17);
v___x_675_ = lean_st_mk_ref(v___x_674_);
v___x_676_ = l_Lean_Compiler_LCNF_toLCNFType(v___x_671_, v___x_673_, v___x_675_, v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v___x_676_, 1);
v___x_678_ = lean_st_ref_get(v___x_675_);
lean_dec(v___x_675_);
lean_dec(v___x_678_);
v___x_679_ = lean_unbox(v_a_665_);
lean_dec(v_a_665_);
v___y_602_ = v_val_670_;
v___y_603_ = v___y_660_;
v___y_604_ = v___x_679_;
v___y_605_ = v_val_663_;
v___y_606_ = v___x_672_;
v___y_607_ = v___x_668_;
v_a_608_ = v_a_677_;
goto v___jp_601_;
}
else
{
lean_dec(v___x_675_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_680_; uint8_t v___x_681_; 
v_a_680_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_680_);
lean_dec_ref_known(v___x_676_, 1);
v___x_681_ = lean_unbox(v_a_665_);
lean_dec(v_a_665_);
v___y_602_ = v_val_670_;
v___y_603_ = v___y_660_;
v___y_604_ = v___x_681_;
v___y_605_ = v_val_663_;
v___y_606_ = v___x_672_;
v___y_607_ = v___x_668_;
v_a_608_ = v_a_680_;
goto v___jp_601_;
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec(v_val_670_);
lean_dec(v___x_668_);
lean_dec(v_a_665_);
lean_dec(v_val_663_);
lean_dec(v___y_660_);
v_a_682_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_676_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_676_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
}
else
{
uint8_t v___x_690_; uint8_t v___x_691_; 
lean_dec(v___x_669_);
lean_inc(v___y_660_);
lean_inc_ref(v_env_667_);
v___x_690_ = l_Lean_hasInitAttr(v_env_667_, v___y_660_);
v___x_691_ = 1;
if (v___x_690_ == 0)
{
lean_object* v___x_692_; 
lean_inc(v_val_663_);
v___x_692_ = l_Lean_ConstantInfo_value_x3f(v_val_663_, v___x_691_);
if (lean_obj_tag(v___x_692_) == 1)
{
lean_object* v_val_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___f_696_; lean_object* v___x_697_; uint8_t v___x_698_; uint8_t v___x_699_; uint8_t v___x_700_; lean_object* v___x_701_; uint64_t v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_val_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_val_693_);
lean_dec_ref_known(v___x_692_, 1);
v___x_694_ = lean_box(v___x_690_);
v___x_695_ = lean_box(v___x_691_);
v___f_696_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toDecl___lam__1___boxed), 9, 2);
lean_closure_set(v___f_696_, 0, v___x_694_);
lean_closure_set(v___f_696_, 1, v___x_695_);
v___x_697_ = l_Lean_ConstantInfo_type(v_val_663_);
v___x_698_ = 1;
v___x_699_ = 0;
v___x_700_ = 2;
v___x_701_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_701_, 0, v___x_690_);
lean_ctor_set_uint8(v___x_701_, 1, v___x_690_);
lean_ctor_set_uint8(v___x_701_, 2, v___x_690_);
lean_ctor_set_uint8(v___x_701_, 3, v___x_690_);
lean_ctor_set_uint8(v___x_701_, 4, v___x_690_);
lean_ctor_set_uint8(v___x_701_, 5, v___x_691_);
lean_ctor_set_uint8(v___x_701_, 6, v___x_691_);
lean_ctor_set_uint8(v___x_701_, 7, v___x_690_);
lean_ctor_set_uint8(v___x_701_, 8, v___x_691_);
lean_ctor_set_uint8(v___x_701_, 9, v___x_698_);
lean_ctor_set_uint8(v___x_701_, 10, v___x_699_);
lean_ctor_set_uint8(v___x_701_, 11, v___x_691_);
lean_ctor_set_uint8(v___x_701_, 12, v___x_691_);
lean_ctor_set_uint8(v___x_701_, 13, v___x_691_);
lean_ctor_set_uint8(v___x_701_, 14, v___x_700_);
lean_ctor_set_uint8(v___x_701_, 15, v___x_691_);
lean_ctor_set_uint8(v___x_701_, 16, v___x_691_);
lean_ctor_set_uint8(v___x_701_, 17, v___x_691_);
lean_ctor_set_uint8(v___x_701_, 18, v___x_691_);
lean_ctor_set_uint8(v___x_701_, 19, v___x_690_);
v___x_702_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_701_);
v___x_703_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set_uint64(v___x_703_, sizeof(void*)*1, v___x_702_);
v___x_704_ = lean_unsigned_to_nat(0u);
v___x_705_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__11, &l_Lean_Compiler_LCNF_toDecl___closed__11_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__11);
v___x_706_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__12));
v___x_707_ = lean_box(0);
v___x_708_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_708_, 0, v___x_703_);
lean_ctor_set(v___x_708_, 1, v___x_658_);
lean_ctor_set(v___x_708_, 2, v___x_705_);
lean_ctor_set(v___x_708_, 3, v___x_706_);
lean_ctor_set(v___x_708_, 4, v___x_707_);
lean_ctor_set(v___x_708_, 5, v___x_704_);
lean_ctor_set(v___x_708_, 6, v___x_707_);
lean_ctor_set_uint8(v___x_708_, sizeof(void*)*7, v___x_690_);
lean_ctor_set_uint8(v___x_708_, sizeof(void*)*7 + 1, v___x_690_);
lean_ctor_set_uint8(v___x_708_, sizeof(void*)*7 + 2, v___x_690_);
lean_ctor_set_uint8(v___x_708_, sizeof(void*)*7 + 3, v___x_691_);
v___x_709_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__17, &l_Lean_Compiler_LCNF_toDecl___closed__17_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__17);
v___x_710_ = lean_st_mk_ref(v___x_709_);
v___x_711_ = l_Lean_Compiler_LCNF_toLCNFType(v___x_697_, v___x_708_, v___x_710_, v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_713_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref_known(v___x_711_, 1);
v___x_713_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v_val_693_, v___f_696_, v___x_690_, v___x_708_, v___x_710_, v_a_485_, v_a_486_);
lean_dec_ref_known(v___x_708_, 7);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_714_);
lean_dec_ref_known(v___x_713_, 1);
v___x_715_ = lean_st_ref_get(v___x_710_);
lean_dec(v___x_710_);
lean_dec(v___x_715_);
lean_inc(v_a_712_);
v___x_716_ = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(v_a_714_, v_a_712_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_716_, 1);
if (lean_obj_tag(v_a_717_) == 1)
{
lean_object* v_k_718_; 
v_k_718_ = lean_ctor_get(v_a_717_, 1);
lean_inc_ref(v_k_718_);
if (lean_obj_tag(v_k_718_) == 5)
{
lean_object* v_decl_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_742_; 
v_decl_719_ = lean_ctor_get(v_a_717_, 0);
lean_inc_ref(v_decl_719_);
lean_dec_ref_known(v_a_717_, 2);
v_isSharedCheck_742_ = !lean_is_exclusive(v_k_718_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; 
v_unused_743_ = lean_ctor_get(v_k_718_, 0);
lean_dec(v_unused_743_);
v___x_721_ = v_k_718_;
v_isShared_722_ = v_isSharedCheck_742_;
goto v_resetjp_720_;
}
else
{
lean_dec(v_k_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_742_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
uint8_t v___x_723_; lean_object* v___x_724_; 
v___x_723_ = 0;
v___x_724_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v___x_723_, v_decl_719_, v___x_690_, v_a_484_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_params_725_; lean_object* v_value_726_; lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; lean_object* v___x_731_; 
lean_dec_ref_known(v___x_724_, 1);
v_params_725_ = lean_ctor_get(v_decl_719_, 2);
lean_inc_ref(v_params_725_);
v_value_726_ = lean_ctor_get(v_decl_719_, 4);
lean_inc_ref(v_value_726_);
lean_dec_ref(v_decl_719_);
v___x_727_ = l_Lean_ConstantInfo_levelParams(v_val_663_);
lean_dec(v_val_663_);
v___x_728_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_728_, 0, v___y_660_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
lean_ctor_set(v___x_728_, 2, v_a_712_);
lean_ctor_set(v___x_728_, 3, v_params_725_);
v___x_729_ = lean_unbox(v_a_665_);
lean_dec(v_a_665_);
lean_ctor_set_uint8(v___x_728_, sizeof(void*)*4, v___x_729_);
if (v_isShared_722_ == 0)
{
lean_ctor_set_tag(v___x_721_, 0);
lean_ctor_set(v___x_721_, 0, v_value_726_);
v___x_731_ = v___x_721_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_value_726_);
v___x_731_ = v_reuseFailAlloc_733_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_732_; 
v___x_732_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_732_, 0, v___x_728_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
lean_ctor_set(v___x_732_, 2, v___x_668_);
lean_ctor_set_uint8(v___x_732_, sizeof(void*)*3, v___x_690_);
v___y_531_ = v_env_667_;
v___y_532_ = v___x_704_;
v___y_533_ = v___x_690_;
v_decl_534_ = v___x_732_;
v___y_535_ = v_a_483_;
v___y_536_ = v_a_484_;
v___y_537_ = v_a_485_;
v___y_538_ = v_a_486_;
goto v___jp_530_;
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_del_object(v___x_721_);
lean_dec_ref(v_decl_719_);
lean_dec(v_a_712_);
lean_dec(v___x_668_);
lean_dec_ref(v_env_667_);
lean_dec(v_a_665_);
lean_dec(v_val_663_);
lean_dec(v___y_660_);
v_a_734_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_724_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_724_);
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
}
else
{
uint8_t v___x_744_; 
lean_dec_ref(v_k_718_);
v___x_744_ = lean_unbox(v_a_665_);
lean_dec(v_a_665_);
v___y_583_ = v___y_660_;
v___y_584_ = v___x_744_;
v___y_585_ = v_val_663_;
v___y_586_ = v_env_667_;
v___y_587_ = v___x_704_;
v___y_588_ = v___x_690_;
v___y_589_ = v_a_717_;
v___y_590_ = v_a_712_;
v___y_591_ = v___x_668_;
v___y_592_ = v_a_483_;
v___y_593_ = v_a_484_;
v___y_594_ = v_a_485_;
v___y_595_ = v_a_486_;
goto v___jp_582_;
}
}
else
{
uint8_t v___x_745_; 
v___x_745_ = lean_unbox(v_a_665_);
lean_dec(v_a_665_);
v___y_583_ = v___y_660_;
v___y_584_ = v___x_745_;
v___y_585_ = v_val_663_;
v___y_586_ = v_env_667_;
v___y_587_ = v___x_704_;
v___y_588_ = v___x_690_;
v___y_589_ = v_a_717_;
v___y_590_ = v_a_712_;
v___y_591_ = v___x_668_;
v___y_592_ = v_a_483_;
v___y_593_ = v_a_484_;
v___y_594_ = v_a_485_;
v___y_595_ = v_a_486_;
goto v___jp_582_;
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec(v_a_712_);
lean_dec(v___x_668_);
lean_dec_ref(v_env_667_);
lean_dec(v_a_665_);
lean_dec(v_val_663_);
lean_dec(v___y_660_);
v_a_746_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_716_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_716_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec(v_a_712_);
lean_dec(v___x_710_);
lean_dec(v___x_668_);
lean_dec_ref(v_env_667_);
lean_dec(v_a_665_);
lean_dec(v_val_663_);
lean_dec(v___y_660_);
v_a_754_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_713_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_713_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec(v___x_710_);
lean_dec_ref_known(v___x_708_, 7);
lean_dec_ref(v___f_696_);
lean_dec(v_val_693_);
lean_dec(v___x_668_);
lean_dec_ref(v_env_667_);
lean_dec(v_a_665_);
lean_dec(v_val_663_);
lean_dec(v___y_660_);
v_a_762_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_711_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_711_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
lean_dec(v___x_692_);
lean_dec(v___x_668_);
lean_dec_ref(v_env_667_);
lean_dec(v_a_665_);
lean_dec(v_val_663_);
v___x_770_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__19, &l_Lean_Compiler_LCNF_toDecl___closed__19_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__19);
v___x_771_ = l_Lean_MessageData_ofConstName(v___y_660_, v___x_690_);
v___x_772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_770_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__21, &l_Lean_Compiler_LCNF_toDecl___closed__21_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__21);
v___x_774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_772_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v___x_774_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
return v___x_775_;
}
}
else
{
lean_object* v___x_776_; uint8_t v___x_777_; uint8_t v___x_778_; uint8_t v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; uint64_t v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
lean_dec_ref(v_env_667_);
v___x_776_ = l_Lean_ConstantInfo_type(v_val_663_);
v___x_777_ = 0;
v___x_778_ = 1;
v___x_779_ = 0;
v___x_780_ = 2;
v___x_781_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_781_, 0, v___x_777_);
lean_ctor_set_uint8(v___x_781_, 1, v___x_777_);
lean_ctor_set_uint8(v___x_781_, 2, v___x_777_);
lean_ctor_set_uint8(v___x_781_, 3, v___x_777_);
lean_ctor_set_uint8(v___x_781_, 4, v___x_777_);
lean_ctor_set_uint8(v___x_781_, 5, v___x_690_);
lean_ctor_set_uint8(v___x_781_, 6, v___x_690_);
lean_ctor_set_uint8(v___x_781_, 7, v___x_777_);
lean_ctor_set_uint8(v___x_781_, 8, v___x_690_);
lean_ctor_set_uint8(v___x_781_, 9, v___x_778_);
lean_ctor_set_uint8(v___x_781_, 10, v___x_779_);
lean_ctor_set_uint8(v___x_781_, 11, v___x_690_);
lean_ctor_set_uint8(v___x_781_, 12, v___x_690_);
lean_ctor_set_uint8(v___x_781_, 13, v___x_690_);
lean_ctor_set_uint8(v___x_781_, 14, v___x_780_);
lean_ctor_set_uint8(v___x_781_, 15, v___x_690_);
lean_ctor_set_uint8(v___x_781_, 16, v___x_690_);
lean_ctor_set_uint8(v___x_781_, 17, v___x_690_);
lean_ctor_set_uint8(v___x_781_, 18, v___x_690_);
lean_ctor_set_uint8(v___x_781_, 19, v___x_777_);
v___x_782_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_781_);
v___x_783_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_783_, 0, v___x_781_);
lean_ctor_set_uint64(v___x_783_, sizeof(void*)*1, v___x_782_);
v___x_784_ = lean_unsigned_to_nat(0u);
v___x_785_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__11, &l_Lean_Compiler_LCNF_toDecl___closed__11_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__11);
v___x_786_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__12));
v___x_787_ = lean_box(0);
v___x_788_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_788_, 0, v___x_783_);
lean_ctor_set(v___x_788_, 1, v___x_658_);
lean_ctor_set(v___x_788_, 2, v___x_785_);
lean_ctor_set(v___x_788_, 3, v___x_786_);
lean_ctor_set(v___x_788_, 4, v___x_787_);
lean_ctor_set(v___x_788_, 5, v___x_784_);
lean_ctor_set(v___x_788_, 6, v___x_787_);
lean_ctor_set_uint8(v___x_788_, sizeof(void*)*7, v___x_777_);
lean_ctor_set_uint8(v___x_788_, sizeof(void*)*7 + 1, v___x_777_);
lean_ctor_set_uint8(v___x_788_, sizeof(void*)*7 + 2, v___x_777_);
lean_ctor_set_uint8(v___x_788_, sizeof(void*)*7 + 3, v___x_691_);
v___x_789_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__17, &l_Lean_Compiler_LCNF_toDecl___closed__17_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__17);
v___x_790_ = lean_st_mk_ref(v___x_789_);
v___x_791_ = l_Lean_Compiler_LCNF_toLCNFType(v___x_776_, v___x_788_, v___x_790_, v_a_485_, v_a_486_);
lean_dec_ref_known(v___x_788_, 7);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v___x_793_ = lean_st_ref_get(v___x_790_);
lean_dec(v___x_790_);
lean_dec(v___x_793_);
v___x_794_ = lean_unbox(v_a_665_);
lean_dec(v_a_665_);
v___y_631_ = v___y_660_;
v___y_632_ = v___x_794_;
v___y_633_ = v_val_663_;
v___y_634_ = v___x_777_;
v___y_635_ = v___x_668_;
v_a_636_ = v_a_792_;
goto v___jp_630_;
}
else
{
lean_dec(v___x_790_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_795_; uint8_t v___x_796_; 
v_a_795_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_795_);
lean_dec_ref_known(v___x_791_, 1);
v___x_796_ = lean_unbox(v_a_665_);
lean_dec(v_a_665_);
v___y_631_ = v___y_660_;
v___y_632_ = v___x_796_;
v___y_633_ = v_val_663_;
v___y_634_ = v___x_777_;
v___y_635_ = v___x_668_;
v_a_636_ = v_a_795_;
goto v___jp_630_;
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec(v___x_668_);
lean_dec(v_a_665_);
lean_dec(v_val_663_);
lean_dec(v___y_660_);
v_a_797_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_791_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_791_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_805_; uint8_t v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec(v_a_662_);
v___x_805_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__19, &l_Lean_Compiler_LCNF_toDecl___closed__19_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__19);
v___x_806_ = 0;
v___x_807_ = l_Lean_MessageData_ofConstName(v___y_660_, v___x_806_);
v___x_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_805_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__23, &l_Lean_Compiler_LCNF_toDecl___closed__23_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__23);
v___x_810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_808_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v___x_810_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
return v___x_811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___boxed(lean_object* v_declName_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_Compiler_LCNF_toDecl(v_declName_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1(uint8_t v___x_821_, lean_object* v_inst_822_, lean_object* v_a_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_821_, v_a_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___boxed(lean_object* v___x_830_, lean_object* v_inst_831_, lean_object* v_a_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
uint8_t v___x_14834__boxed_838_; lean_object* v_res_839_; 
v___x_14834__boxed_838_ = lean_unbox(v___x_830_);
v_res_839_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1(v___x_14834__boxed_838_, v_inst_831_, v_a_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4(uint8_t v___x_840_, size_t v_sz_841_, size_t v_i_842_, lean_object* v_bs_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___x_840_, v_sz_841_, v_i_842_, v_bs_843_, v___y_845_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___boxed(lean_object* v___x_850_, lean_object* v_sz_851_, lean_object* v_i_852_, lean_object* v_bs_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
uint8_t v___x_14857__boxed_859_; size_t v_sz_boxed_860_; size_t v_i_boxed_861_; lean_object* v_res_862_; 
v___x_14857__boxed_859_ = lean_unbox(v___x_850_);
v_sz_boxed_860_ = lean_unbox_usize(v_sz_851_);
lean_dec(v_sz_851_);
v_i_boxed_861_ = lean_unbox_usize(v_i_852_);
lean_dec(v_i_852_);
v_res_862_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4(v___x_14857__boxed_859_, v_sz_boxed_860_, v_i_boxed_861_, v_bs_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
return v_res_862_;
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
