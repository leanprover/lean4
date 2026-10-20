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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedBorrowed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
lean_object* l_Lean_Compiler_mkUnsafeRecName(lean_object*);
uint8_t l_Lean_isExport(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
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
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(uint8_t, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Compiler_LCNF_toDecl___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declaration `"};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__17 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__17_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__18;
static const lean_string_object l_Lean_Compiler_LCNF_toDecl___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "` does not have a value"};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__19 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__19_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__20;
static const lean_ctor_object l_Lean_Compiler_LCNF_toDecl___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__21 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__21_value;
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
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_99_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___closed__0);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_102_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_103_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___closed__1);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg(lean_object* v_msg_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
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
v___x_128_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___closed__2, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___closed__2_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___closed__2);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___boxed(lean_object* v_msg_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg(v_msg_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3(lean_object* v_00_u03b1_155_, lean_object* v_msg_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg(v_msg_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___boxed(lean_object* v_00_u03b1_163_, lean_object* v_msg_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3(v_00_u03b1_163_, v_msg_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0(lean_object* v_k_171_, lean_object* v_b_172_, lean_object* v_c_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0___boxed(lean_object* v_k_180_, lean_object* v_b_181_, lean_object* v_c_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0(v_k_180_, v_b_181_, v_c_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(lean_object* v_e_189_, lean_object* v_k_190_, uint8_t v_cleanupAnnotations_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v___f_197_; uint8_t v___x_198_; uint8_t v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___f_197_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0___boxed), 8, 1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___boxed(lean_object* v_e_218_, lean_object* v_k_219_, lean_object* v_cleanupAnnotations_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_226_; lean_object* v_res_227_; 
v_cleanupAnnotations_boxed_226_ = lean_unbox(v_cleanupAnnotations_220_);
v_res_227_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v_e_218_, v_k_219_, v_cleanupAnnotations_boxed_226_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5(lean_object* v_00_u03b1_228_, lean_object* v_e_229_, lean_object* v_k_230_, uint8_t v_cleanupAnnotations_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v_e_229_, v_k_230_, v_cleanupAnnotations_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___boxed(lean_object* v_00_u03b1_238_, lean_object* v_e_239_, lean_object* v_k_240_, lean_object* v_cleanupAnnotations_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_247_; lean_object* v_res_248_; 
v_cleanupAnnotations_boxed_247_ = lean_unbox(v_cleanupAnnotations_241_);
v_res_248_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5(v_00_u03b1_238_, v_e_239_, v_k_240_, v_cleanupAnnotations_boxed_247_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
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
uint8_t v___x_13651__boxed_303_; lean_object* v_res_304_; 
v___x_13651__boxed_303_ = lean_unbox(v___x_296_);
v_res_304_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_13651__boxed_303_, v_a_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
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
uint8_t v___x_13809__boxed_365_; uint8_t v___x_13810__boxed_366_; lean_object* v_res_367_; 
v___x_13809__boxed_365_ = lean_unbox(v___x_356_);
v___x_13810__boxed_366_ = lean_unbox(v___x_357_);
v_res_367_ = l_Lean_Compiler_LCNF_toDecl___lam__1(v___x_13809__boxed_365_, v___x_13810__boxed_366_, v_xs_358_, v_body_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec_ref(v_xs_358_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(uint8_t v___x_368_, size_t v_sz_369_, size_t v_i_370_, lean_object* v_bs_371_, lean_object* v___y_372_){
_start:
{
uint8_t v___x_374_; 
v___x_374_ = lean_usize_dec_lt(v_i_370_, v_sz_369_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; 
v___x_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_375_, 0, v_bs_371_);
return v___x_375_;
}
else
{
lean_object* v_v_376_; lean_object* v___x_377_; lean_object* v_bs_x27_378_; uint8_t v___x_379_; lean_object* v___x_380_; 
v_v_376_ = lean_array_uget(v_bs_371_, v_i_370_);
v___x_377_ = lean_unsigned_to_nat(0u);
v_bs_x27_378_ = lean_array_uset(v_bs_371_, v_i_370_, v___x_377_);
v___x_379_ = 0;
v___x_380_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v___x_379_, v_v_376_, v___x_368_, v___y_372_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; size_t v___x_382_; size_t v___x_383_; lean_object* v___x_384_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v___x_380_, 1);
v___x_382_ = ((size_t)1ULL);
v___x_383_ = lean_usize_add(v_i_370_, v___x_382_);
v___x_384_ = lean_array_uset(v_bs_x27_378_, v_i_370_, v_a_381_);
v_i_370_ = v___x_383_;
v_bs_371_ = v___x_384_;
goto _start;
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_dec_ref(v_bs_x27_378_);
v_a_386_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_380_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_380_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___boxed(lean_object* v___x_394_, lean_object* v_sz_395_, lean_object* v_i_396_, lean_object* v_bs_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
uint8_t v___x_13839__boxed_400_; size_t v_sz_boxed_401_; size_t v_i_boxed_402_; lean_object* v_res_403_; 
v___x_13839__boxed_400_ = lean_unbox(v___x_394_);
v_sz_boxed_401_ = lean_unbox_usize(v_sz_395_);
lean_dec(v_sz_395_);
v_i_boxed_402_ = lean_unbox_usize(v_i_396_);
lean_dec(v_i_396_);
v_res_403_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___x_13839__boxed_400_, v_sz_boxed_401_, v_i_boxed_402_, v_bs_397_, v___y_398_);
lean_dec(v___y_398_);
return v_res_403_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__2(lean_object* v_as_404_, size_t v_i_405_, size_t v_stop_406_){
_start:
{
uint8_t v___x_407_; 
v___x_407_ = lean_usize_dec_eq(v_i_405_, v_stop_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; uint8_t v_borrow_409_; 
v___x_408_ = lean_array_uget_borrowed(v_as_404_, v_i_405_);
v_borrow_409_ = lean_ctor_get_uint8(v___x_408_, sizeof(void*)*3);
if (v_borrow_409_ == 0)
{
size_t v___x_410_; size_t v___x_411_; 
v___x_410_ = ((size_t)1ULL);
v___x_411_ = lean_usize_add(v_i_405_, v___x_410_);
v_i_405_ = v___x_411_;
goto _start;
}
else
{
return v_borrow_409_;
}
}
else
{
uint8_t v___x_413_; 
v___x_413_ = 0;
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__2___boxed(lean_object* v_as_414_, lean_object* v_i_415_, lean_object* v_stop_416_){
_start:
{
size_t v_i_boxed_417_; size_t v_stop_boxed_418_; uint8_t v_res_419_; lean_object* v_r_420_; 
v_i_boxed_417_ = lean_unbox_usize(v_i_415_);
lean_dec(v_i_415_);
v_stop_boxed_418_ = lean_unbox_usize(v_stop_416_);
lean_dec(v_stop_416_);
v_res_419_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__2(v_as_414_, v_i_boxed_417_, v_stop_boxed_418_);
lean_dec_ref(v_as_414_);
v_r_420_ = lean_box(v_res_419_);
return v_r_420_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__1(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__0));
v___x_423_ = l_Lean_stringToMessageData(v___x_422_);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__3(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__2));
v___x_426_ = l_Lean_stringToMessageData(v___x_425_);
return v___x_426_;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_toDecl___closed__5(void){
_start:
{
lean_object* v___x_433_; uint64_t v___x_434_; 
v___x_433_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__4));
v___x_434_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_433_);
return v___x_434_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__6(void){
_start:
{
uint64_t v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = lean_uint64_once(&l_Lean_Compiler_LCNF_toDecl___closed__5, &l_Lean_Compiler_LCNF_toDecl___closed__5_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__5);
v___x_436_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__4));
v___x_437_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set_uint64(v___x_437_, sizeof(void*)*1, v___x_435_);
return v___x_437_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__7(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg___closed__0);
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__8(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_unsigned_to_nat(32u);
v___x_441_ = lean_mk_empty_array_with_capacity(v___x_440_);
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__9(void){
_start:
{
size_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_443_ = ((size_t)5ULL);
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = lean_unsigned_to_nat(32u);
v___x_446_ = lean_mk_empty_array_with_capacity(v___x_445_);
v___x_447_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__8, &l_Lean_Compiler_LCNF_toDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__8);
v___x_448_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v___x_446_);
lean_ctor_set(v___x_448_, 2, v___x_444_);
lean_ctor_set(v___x_448_, 3, v___x_444_);
lean_ctor_set_usize(v___x_448_, 4, v___x_443_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__10(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_449_ = lean_box(1);
v___x_450_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__9, &l_Lean_Compiler_LCNF_toDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__9);
v___x_451_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__7, &l_Lean_Compiler_LCNF_toDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__7);
v___x_452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
lean_ctor_set(v___x_452_, 1, v___x_450_);
lean_ctor_set(v___x_452_, 2, v___x_449_);
return v___x_452_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__12(void){
_start:
{
uint8_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_455_ = 1;
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = lean_box(0);
v___x_458_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__11));
v___x_459_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__10, &l_Lean_Compiler_LCNF_toDecl___closed__10_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__10);
v___x_460_ = lean_box(1);
v___x_461_ = 0;
v___x_462_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__6, &l_Lean_Compiler_LCNF_toDecl___closed__6_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__6);
v___x_463_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v___x_460_);
lean_ctor_set(v___x_463_, 2, v___x_459_);
lean_ctor_set(v___x_463_, 3, v___x_458_);
lean_ctor_set(v___x_463_, 4, v___x_457_);
lean_ctor_set(v___x_463_, 5, v___x_456_);
lean_ctor_set(v___x_463_, 6, v___x_457_);
lean_ctor_set_uint8(v___x_463_, sizeof(void*)*7, v___x_461_);
lean_ctor_set_uint8(v___x_463_, sizeof(void*)*7 + 1, v___x_461_);
lean_ctor_set_uint8(v___x_463_, sizeof(void*)*7 + 2, v___x_461_);
lean_ctor_set_uint8(v___x_463_, sizeof(void*)*7 + 3, v___x_455_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__13(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_464_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_465_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__7, &l_Lean_Compiler_LCNF_toDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__7);
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
lean_ctor_set(v___x_467_, 2, v___x_466_);
lean_ctor_set(v___x_467_, 3, v___x_466_);
lean_ctor_set(v___x_467_, 4, v___x_465_);
lean_ctor_set(v___x_467_, 5, v___x_465_);
lean_ctor_set(v___x_467_, 6, v___x_465_);
lean_ctor_set(v___x_467_, 7, v___x_465_);
lean_ctor_set(v___x_467_, 8, v___x_465_);
lean_ctor_set(v___x_467_, 9, v___x_465_);
lean_ctor_set(v___x_467_, 10, v___x_465_);
lean_ctor_set(v___x_467_, 11, v___x_464_);
return v___x_467_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__14(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__7, &l_Lean_Compiler_LCNF_toDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__7);
v___x_469_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
lean_ctor_set(v___x_469_, 2, v___x_468_);
lean_ctor_set(v___x_469_, 3, v___x_468_);
lean_ctor_set(v___x_469_, 4, v___x_468_);
lean_ctor_set(v___x_469_, 5, v___x_468_);
return v___x_469_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__15(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_470_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__7, &l_Lean_Compiler_LCNF_toDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__7);
v___x_471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
lean_ctor_set(v___x_471_, 2, v___x_470_);
lean_ctor_set(v___x_471_, 3, v___x_470_);
lean_ctor_set(v___x_471_, 4, v___x_470_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__16(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_472_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__15, &l_Lean_Compiler_LCNF_toDecl___closed__15_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__15);
v___x_473_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__9, &l_Lean_Compiler_LCNF_toDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__9);
v___x_474_ = lean_box(1);
v___x_475_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__14, &l_Lean_Compiler_LCNF_toDecl___closed__14_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__14);
v___x_476_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__13, &l_Lean_Compiler_LCNF_toDecl___closed__13_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__13);
v___x_477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___x_475_);
lean_ctor_set(v___x_477_, 2, v___x_474_);
lean_ctor_set(v___x_477_, 3, v___x_473_);
lean_ctor_set(v___x_477_, 4, v___x_472_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__18(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__17));
v___x_480_ = l_Lean_stringToMessageData(v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__20(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__19));
v___x_483_ = l_Lean_stringToMessageData(v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__23(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__22));
v___x_488_ = l_Lean_stringToMessageData(v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object* v_declName_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v_decl_498_; lean_object* v_name_499_; lean_object* v_params_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_530_; lean_object* v___y_531_; uint8_t v___y_532_; lean_object* v_decl_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; uint8_t v___y_587_; uint8_t v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___x_600_; lean_object* v___y_602_; lean_object* v___x_798_; 
v___x_600_ = lean_box(1);
v___x_798_ = l_Lean_Compiler_isUnsafeRecName_x3f(v_declName_489_);
if (lean_obj_tag(v___x_798_) == 1)
{
lean_object* v_val_799_; 
lean_dec(v_declName_489_);
v_val_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_val_799_);
lean_dec_ref_known(v___x_798_, 1);
v___y_602_ = v_val_799_;
goto v___jp_601_;
}
else
{
lean_dec(v___x_798_);
v___y_602_ = v_declName_489_;
goto v___jp_601_;
}
v___jp_495_:
{
uint8_t v___x_505_; 
lean_inc(v_name_499_);
v___x_505_ = l_Lean_isExport(v___y_497_, v_name_499_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; 
lean_dec_ref(v_params_500_);
lean_dec(v_name_499_);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v_decl_498_);
return v___x_506_;
}
else
{
lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_507_ = lean_array_get_size(v_params_500_);
v___x_508_ = lean_nat_dec_lt(v___y_496_, v___x_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
lean_dec_ref(v_params_500_);
lean_dec(v_name_499_);
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v_decl_498_);
return v___x_509_;
}
else
{
if (v___x_508_ == 0)
{
lean_object* v___x_510_; 
lean_dec_ref(v_params_500_);
lean_dec(v_name_499_);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v_decl_498_);
return v___x_510_;
}
else
{
size_t v___x_511_; size_t v___x_512_; uint8_t v___x_513_; 
v___x_511_ = ((size_t)0ULL);
v___x_512_ = lean_usize_of_nat(v___x_507_);
v___x_513_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__2(v_params_500_, v___x_511_, v___x_512_);
lean_dec_ref(v_params_500_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
lean_dec(v_name_499_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v_decl_498_);
return v___x_514_;
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
lean_dec_ref(v_decl_498_);
v___x_515_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__1, &l_Lean_Compiler_LCNF_toDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__1);
v___x_516_ = l_Lean_MessageData_ofName(v_name_499_);
v___x_517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__3, &l_Lean_Compiler_LCNF_toDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__3);
v___x_519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_517_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg(v___x_519_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
v_a_521_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
}
}
}
v___jp_529_:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Compiler_LCNF_Decl_etaExpand(v_decl_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v___x_538_, 1);
v___x_540_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_536_);
v___x_541_ = l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
v___x_542_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(v___x_540_, v___x_541_);
lean_dec_ref(v___x_540_);
if (v___x_542_ == 0)
{
lean_object* v_toSignature_543_; lean_object* v_name_544_; lean_object* v_params_545_; 
v_toSignature_543_ = lean_ctor_get(v_a_539_, 0);
v_name_544_ = lean_ctor_get(v_toSignature_543_, 0);
lean_inc(v_name_544_);
v_params_545_ = lean_ctor_get(v_toSignature_543_, 3);
lean_inc_ref(v_params_545_);
v___y_496_ = v___y_530_;
v___y_497_ = v___y_531_;
v_decl_498_ = v_a_539_;
v_name_499_ = v_name_544_;
v_params_500_ = v_params_545_;
v___y_501_ = v___y_534_;
v___y_502_ = v___y_535_;
v___y_503_ = v___y_536_;
v___y_504_ = v___y_537_;
goto v___jp_495_;
}
else
{
lean_object* v_toSignature_546_; lean_object* v_value_547_; uint8_t v_recursive_548_; lean_object* v_inlineAttr_x3f_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_580_; 
v_toSignature_546_ = lean_ctor_get(v_a_539_, 0);
v_value_547_ = lean_ctor_get(v_a_539_, 1);
v_recursive_548_ = lean_ctor_get_uint8(v_a_539_, sizeof(void*)*3);
v_inlineAttr_x3f_549_ = lean_ctor_get(v_a_539_, 2);
v_isSharedCheck_580_ = !lean_is_exclusive(v_a_539_);
if (v_isSharedCheck_580_ == 0)
{
v___x_551_ = v_a_539_;
v_isShared_552_ = v_isSharedCheck_580_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_inlineAttr_x3f_549_);
lean_inc(v_value_547_);
lean_inc(v_toSignature_546_);
lean_dec(v_a_539_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_580_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v_name_553_; lean_object* v_levelParams_554_; lean_object* v_type_555_; lean_object* v_params_556_; uint8_t v_safe_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_579_; 
v_name_553_ = lean_ctor_get(v_toSignature_546_, 0);
v_levelParams_554_ = lean_ctor_get(v_toSignature_546_, 1);
v_type_555_ = lean_ctor_get(v_toSignature_546_, 2);
v_params_556_ = lean_ctor_get(v_toSignature_546_, 3);
v_safe_557_ = lean_ctor_get_uint8(v_toSignature_546_, sizeof(void*)*4);
v_isSharedCheck_579_ = !lean_is_exclusive(v_toSignature_546_);
if (v_isSharedCheck_579_ == 0)
{
v___x_559_ = v_toSignature_546_;
v_isShared_560_ = v_isSharedCheck_579_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_params_556_);
lean_inc(v_type_555_);
lean_inc(v_levelParams_554_);
lean_inc(v_name_553_);
lean_dec(v_toSignature_546_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_579_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
size_t v_sz_561_; size_t v___x_562_; lean_object* v___x_563_; 
v_sz_561_ = lean_array_size(v_params_556_);
v___x_562_ = ((size_t)0ULL);
v___x_563_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___y_532_, v_sz_561_, v___x_562_, v_params_556_, v___y_535_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_566_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc_n(v_a_564_, 2);
lean_dec_ref_known(v___x_563_, 1);
lean_inc(v_name_553_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 3, v_a_564_);
v___x_566_ = v___x_559_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_name_553_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_levelParams_554_);
lean_ctor_set(v_reuseFailAlloc_570_, 2, v_type_555_);
lean_ctor_set(v_reuseFailAlloc_570_, 3, v_a_564_);
lean_ctor_set_uint8(v_reuseFailAlloc_570_, sizeof(void*)*4, v_safe_557_);
v___x_566_ = v_reuseFailAlloc_570_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_568_; 
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_566_);
v___x_568_ = v___x_551_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_value_547_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_inlineAttr_x3f_549_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, sizeof(void*)*3, v_recursive_548_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
v___y_496_ = v___y_530_;
v___y_497_ = v___y_531_;
v_decl_498_ = v___x_568_;
v_name_499_ = v_name_553_;
v_params_500_ = v_a_564_;
v___y_501_ = v___y_534_;
v___y_502_ = v___y_535_;
v___y_503_ = v___y_536_;
v___y_504_ = v___y_537_;
goto v___jp_495_;
}
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_del_object(v___x_559_);
lean_dec_ref(v_type_555_);
lean_dec(v_levelParams_554_);
lean_dec(v_name_553_);
lean_del_object(v___x_551_);
lean_dec(v_inlineAttr_x3f_549_);
lean_dec_ref(v_value_547_);
lean_dec_ref(v___y_531_);
v_a_571_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_563_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_563_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
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
return v___x_538_;
}
}
v___jp_581_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_595_ = l_Lean_ConstantInfo_levelParams(v___y_584_);
lean_dec_ref(v___y_584_);
v___x_596_ = lean_mk_empty_array_with_capacity(v___y_583_);
v___x_597_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_597_, 0, v___y_586_);
lean_ctor_set(v___x_597_, 1, v___x_595_);
lean_ctor_set(v___x_597_, 2, v___y_582_);
lean_ctor_set(v___x_597_, 3, v___x_596_);
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*4, v___y_588_);
v___x_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_598_, 0, v___y_589_);
v___x_599_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
lean_ctor_set(v___x_599_, 2, v___y_590_);
lean_ctor_set_uint8(v___x_599_, sizeof(void*)*3, v___y_587_);
v___y_530_ = v___y_583_;
v___y_531_ = v___y_585_;
v___y_532_ = v___y_587_;
v_decl_533_ = v___x_599_;
v___y_534_ = v___y_591_;
v___y_535_ = v___y_592_;
v___y_536_ = v___y_593_;
v___y_537_ = v___y_594_;
goto v___jp_529_;
}
v___jp_601_:
{
lean_object* v___x_603_; lean_object* v_a_604_; 
lean_inc(v___y_602_);
v___x_603_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(v___y_602_, v_a_493_);
v_a_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_a_604_);
lean_dec_ref(v___x_603_);
if (lean_obj_tag(v_a_604_) == 1)
{
lean_object* v_val_605_; lean_object* v___x_606_; lean_object* v_a_607_; lean_object* v___x_608_; lean_object* v_env_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_val_605_ = lean_ctor_get(v_a_604_, 0);
lean_inc(v_val_605_);
lean_dec_ref_known(v_a_604_, 1);
lean_inc_n(v___y_602_, 3);
v___x_606_ = l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(v___y_602_, v_a_493_);
v_a_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_a_607_);
lean_dec_ref(v___x_606_);
v___x_608_ = lean_st_ref_get(v_a_493_);
v_env_609_ = lean_ctor_get(v___x_608_, 0);
lean_inc_ref_n(v_env_609_, 3);
lean_dec(v___x_608_);
v___x_610_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_609_, v___y_602_);
v___x_611_ = l_Lean_getExternAttrData_x3f(v_env_609_, v___y_602_);
if (lean_obj_tag(v___x_611_) == 1)
{
lean_object* v_val_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_656_; 
lean_dec_ref(v_env_609_);
v_val_612_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_656_ == 0)
{
v___x_614_ = v___x_611_;
v_isShared_615_ = v_isSharedCheck_656_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_val_612_);
lean_dec(v___x_611_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_656_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; uint8_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_616_ = l_Lean_ConstantInfo_type(v_val_605_);
v___x_617_ = 0;
v___x_618_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__12, &l_Lean_Compiler_LCNF_toDecl___closed__12_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__12);
v___x_619_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__16, &l_Lean_Compiler_LCNF_toDecl___closed__16_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__16);
v___x_620_ = lean_st_mk_ref(v___x_619_);
v___x_621_ = l_Lean_Compiler_LCNF_toLCNFType(v___x_616_, v___x_618_, v___x_620_, v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc_n(v_a_622_, 2);
lean_dec_ref_known(v___x_621_, 1);
v___x_623_ = lean_st_ref_get(v___x_620_);
lean_dec(v___x_620_);
lean_dec(v___x_623_);
v___x_624_ = l_Lean_Compiler_LCNF_toDecl___lam__0(v_a_622_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_639_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_639_ == 0)
{
v___x_627_ = v___x_624_;
v_isShared_628_ = v_isSharedCheck_639_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_639_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; lean_object* v___x_633_; 
v___x_629_ = l_Lean_ConstantInfo_levelParams(v_val_605_);
lean_dec(v_val_605_);
v___x_630_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_630_, 0, v___y_602_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
lean_ctor_set(v___x_630_, 2, v_a_622_);
lean_ctor_set(v___x_630_, 3, v_a_625_);
v___x_631_ = lean_unbox(v_a_607_);
lean_dec(v_a_607_);
lean_ctor_set_uint8(v___x_630_, sizeof(void*)*4, v___x_631_);
if (v_isShared_615_ == 0)
{
v___x_633_ = v___x_614_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_val_612_);
v___x_633_ = v_reuseFailAlloc_638_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_634_; lean_object* v___x_636_; 
v___x_634_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_634_, 0, v___x_630_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
lean_ctor_set(v___x_634_, 2, v___x_610_);
lean_ctor_set_uint8(v___x_634_, sizeof(void*)*3, v___x_617_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_634_);
v___x_636_ = v___x_627_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec(v_a_622_);
lean_del_object(v___x_614_);
lean_dec(v_val_612_);
lean_dec(v___x_610_);
lean_dec(v_a_607_);
lean_dec(v_val_605_);
lean_dec(v___y_602_);
v_a_640_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_624_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_624_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec(v___x_620_);
lean_del_object(v___x_614_);
lean_dec(v_val_612_);
lean_dec(v___x_610_);
lean_dec(v_a_607_);
lean_dec(v_val_605_);
lean_dec(v___y_602_);
v_a_648_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_621_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_621_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
else
{
uint8_t v___x_657_; uint8_t v___x_658_; 
lean_dec(v___x_611_);
lean_inc(v___y_602_);
lean_inc_ref(v_env_609_);
v___x_657_ = l_Lean_hasInitAttr(v_env_609_, v___y_602_);
v___x_658_ = 1;
if (v___x_657_ == 0)
{
lean_object* v___x_659_; 
lean_inc(v_val_605_);
v___x_659_ = l_Lean_ConstantInfo_value_x3f(v_val_605_, v___x_658_);
if (lean_obj_tag(v___x_659_) == 1)
{
lean_object* v_val_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___f_663_; lean_object* v___x_664_; uint8_t v___x_665_; uint8_t v___x_666_; uint8_t v___x_667_; lean_object* v___x_668_; uint64_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v_val_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_val_660_);
lean_dec_ref_known(v___x_659_, 1);
v___x_661_ = lean_box(v___x_657_);
v___x_662_ = lean_box(v___x_658_);
v___f_663_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toDecl___lam__1___boxed), 9, 2);
lean_closure_set(v___f_663_, 0, v___x_661_);
lean_closure_set(v___f_663_, 1, v___x_662_);
v___x_664_ = l_Lean_ConstantInfo_type(v_val_605_);
v___x_665_ = 1;
v___x_666_ = 0;
v___x_667_ = 2;
v___x_668_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_668_, 0, v___x_657_);
lean_ctor_set_uint8(v___x_668_, 1, v___x_657_);
lean_ctor_set_uint8(v___x_668_, 2, v___x_657_);
lean_ctor_set_uint8(v___x_668_, 3, v___x_657_);
lean_ctor_set_uint8(v___x_668_, 4, v___x_657_);
lean_ctor_set_uint8(v___x_668_, 5, v___x_658_);
lean_ctor_set_uint8(v___x_668_, 6, v___x_658_);
lean_ctor_set_uint8(v___x_668_, 7, v___x_657_);
lean_ctor_set_uint8(v___x_668_, 8, v___x_658_);
lean_ctor_set_uint8(v___x_668_, 9, v___x_665_);
lean_ctor_set_uint8(v___x_668_, 10, v___x_666_);
lean_ctor_set_uint8(v___x_668_, 11, v___x_658_);
lean_ctor_set_uint8(v___x_668_, 12, v___x_658_);
lean_ctor_set_uint8(v___x_668_, 13, v___x_658_);
lean_ctor_set_uint8(v___x_668_, 14, v___x_667_);
lean_ctor_set_uint8(v___x_668_, 15, v___x_658_);
lean_ctor_set_uint8(v___x_668_, 16, v___x_658_);
lean_ctor_set_uint8(v___x_668_, 17, v___x_658_);
lean_ctor_set_uint8(v___x_668_, 18, v___x_658_);
lean_ctor_set_uint8(v___x_668_, 19, v___x_657_);
v___x_669_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_668_);
v___x_670_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_670_, 0, v___x_668_);
lean_ctor_set_uint64(v___x_670_, sizeof(void*)*1, v___x_669_);
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__10, &l_Lean_Compiler_LCNF_toDecl___closed__10_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__10);
v___x_673_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__11));
v___x_674_ = lean_box(0);
v___x_675_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_675_, 0, v___x_670_);
lean_ctor_set(v___x_675_, 1, v___x_600_);
lean_ctor_set(v___x_675_, 2, v___x_672_);
lean_ctor_set(v___x_675_, 3, v___x_673_);
lean_ctor_set(v___x_675_, 4, v___x_674_);
lean_ctor_set(v___x_675_, 5, v___x_671_);
lean_ctor_set(v___x_675_, 6, v___x_674_);
lean_ctor_set_uint8(v___x_675_, sizeof(void*)*7, v___x_657_);
lean_ctor_set_uint8(v___x_675_, sizeof(void*)*7 + 1, v___x_657_);
lean_ctor_set_uint8(v___x_675_, sizeof(void*)*7 + 2, v___x_657_);
lean_ctor_set_uint8(v___x_675_, sizeof(void*)*7 + 3, v___x_658_);
v___x_676_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__16, &l_Lean_Compiler_LCNF_toDecl___closed__16_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__16);
v___x_677_ = lean_st_mk_ref(v___x_676_);
v___x_678_ = l_Lean_Compiler_LCNF_toLCNFType(v___x_664_, v___x_675_, v___x_677_, v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v___x_680_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_a_679_);
lean_dec_ref_known(v___x_678_, 1);
v___x_680_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v_val_660_, v___f_663_, v___x_657_, v___x_675_, v___x_677_, v_a_492_, v_a_493_);
lean_dec_ref_known(v___x_675_, 7);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_681_);
lean_dec_ref_known(v___x_680_, 1);
v___x_682_ = lean_st_ref_get(v___x_677_);
lean_dec(v___x_677_);
lean_dec(v___x_682_);
lean_inc(v_a_679_);
v___x_683_ = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(v_a_681_, v_a_679_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_a_684_);
lean_dec_ref_known(v___x_683_, 1);
if (lean_obj_tag(v_a_684_) == 1)
{
lean_object* v_k_685_; 
v_k_685_ = lean_ctor_get(v_a_684_, 1);
lean_inc_ref(v_k_685_);
if (lean_obj_tag(v_k_685_) == 5)
{
lean_object* v_decl_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_709_; 
v_decl_686_ = lean_ctor_get(v_a_684_, 0);
lean_inc_ref(v_decl_686_);
lean_dec_ref_known(v_a_684_, 2);
v_isSharedCheck_709_ = !lean_is_exclusive(v_k_685_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; 
v_unused_710_ = lean_ctor_get(v_k_685_, 0);
lean_dec(v_unused_710_);
v___x_688_ = v_k_685_;
v_isShared_689_ = v_isSharedCheck_709_;
goto v_resetjp_687_;
}
else
{
lean_dec(v_k_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_709_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
uint8_t v___x_690_; lean_object* v___x_691_; 
v___x_690_ = 0;
v___x_691_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v___x_690_, v_decl_686_, v___x_657_, v_a_491_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_params_692_; lean_object* v_value_693_; lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; lean_object* v___x_698_; 
lean_dec_ref_known(v___x_691_, 1);
v_params_692_ = lean_ctor_get(v_decl_686_, 2);
lean_inc_ref(v_params_692_);
v_value_693_ = lean_ctor_get(v_decl_686_, 4);
lean_inc_ref(v_value_693_);
lean_dec_ref(v_decl_686_);
v___x_694_ = l_Lean_ConstantInfo_levelParams(v_val_605_);
lean_dec(v_val_605_);
v___x_695_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_695_, 0, v___y_602_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
lean_ctor_set(v___x_695_, 2, v_a_679_);
lean_ctor_set(v___x_695_, 3, v_params_692_);
v___x_696_ = lean_unbox(v_a_607_);
lean_dec(v_a_607_);
lean_ctor_set_uint8(v___x_695_, sizeof(void*)*4, v___x_696_);
if (v_isShared_689_ == 0)
{
lean_ctor_set_tag(v___x_688_, 0);
lean_ctor_set(v___x_688_, 0, v_value_693_);
v___x_698_ = v___x_688_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_value_693_);
v___x_698_ = v_reuseFailAlloc_700_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; 
v___x_699_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_699_, 0, v___x_695_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
lean_ctor_set(v___x_699_, 2, v___x_610_);
lean_ctor_set_uint8(v___x_699_, sizeof(void*)*3, v___x_657_);
v___y_530_ = v___x_671_;
v___y_531_ = v_env_609_;
v___y_532_ = v___x_657_;
v_decl_533_ = v___x_699_;
v___y_534_ = v_a_490_;
v___y_535_ = v_a_491_;
v___y_536_ = v_a_492_;
v___y_537_ = v_a_493_;
goto v___jp_529_;
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_del_object(v___x_688_);
lean_dec_ref(v_decl_686_);
lean_dec(v_a_679_);
lean_dec(v___x_610_);
lean_dec_ref(v_env_609_);
lean_dec(v_a_607_);
lean_dec(v_val_605_);
lean_dec(v___y_602_);
v_a_701_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_691_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_691_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
else
{
uint8_t v___x_711_; 
lean_dec_ref(v_k_685_);
v___x_711_ = lean_unbox(v_a_607_);
lean_dec(v_a_607_);
v___y_582_ = v_a_679_;
v___y_583_ = v___x_671_;
v___y_584_ = v_val_605_;
v___y_585_ = v_env_609_;
v___y_586_ = v___y_602_;
v___y_587_ = v___x_657_;
v___y_588_ = v___x_711_;
v___y_589_ = v_a_684_;
v___y_590_ = v___x_610_;
v___y_591_ = v_a_490_;
v___y_592_ = v_a_491_;
v___y_593_ = v_a_492_;
v___y_594_ = v_a_493_;
goto v___jp_581_;
}
}
else
{
uint8_t v___x_712_; 
v___x_712_ = lean_unbox(v_a_607_);
lean_dec(v_a_607_);
v___y_582_ = v_a_679_;
v___y_583_ = v___x_671_;
v___y_584_ = v_val_605_;
v___y_585_ = v_env_609_;
v___y_586_ = v___y_602_;
v___y_587_ = v___x_657_;
v___y_588_ = v___x_712_;
v___y_589_ = v_a_684_;
v___y_590_ = v___x_610_;
v___y_591_ = v_a_490_;
v___y_592_ = v_a_491_;
v___y_593_ = v_a_492_;
v___y_594_ = v_a_493_;
goto v___jp_581_;
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec(v_a_679_);
lean_dec(v___x_610_);
lean_dec_ref(v_env_609_);
lean_dec(v_a_607_);
lean_dec(v_val_605_);
lean_dec(v___y_602_);
v_a_713_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_683_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_683_);
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
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec(v_a_679_);
lean_dec(v___x_677_);
lean_dec(v___x_610_);
lean_dec_ref(v_env_609_);
lean_dec(v_a_607_);
lean_dec(v_val_605_);
lean_dec(v___y_602_);
v_a_721_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_680_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_680_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec(v___x_677_);
lean_dec_ref_known(v___x_675_, 7);
lean_dec_ref(v___f_663_);
lean_dec(v_val_660_);
lean_dec(v___x_610_);
lean_dec_ref(v_env_609_);
lean_dec(v_a_607_);
lean_dec(v_val_605_);
lean_dec(v___y_602_);
v_a_729_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_678_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_678_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
lean_dec(v___x_659_);
lean_dec(v___x_610_);
lean_dec_ref(v_env_609_);
lean_dec(v_a_607_);
lean_dec(v_val_605_);
v___x_737_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__18, &l_Lean_Compiler_LCNF_toDecl___closed__18_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__18);
v___x_738_ = l_Lean_MessageData_ofConstName(v___y_602_, v___x_657_);
v___x_739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__20, &l_Lean_Compiler_LCNF_toDecl___closed__20_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__20);
v___x_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_739_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg(v___x_741_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
return v___x_742_;
}
}
else
{
lean_object* v___x_743_; uint8_t v___x_744_; uint8_t v___x_745_; uint8_t v___x_746_; uint8_t v___x_747_; lean_object* v___x_748_; uint64_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
lean_dec_ref(v_env_609_);
v___x_743_ = l_Lean_ConstantInfo_type(v_val_605_);
v___x_744_ = 0;
v___x_745_ = 1;
v___x_746_ = 0;
v___x_747_ = 2;
v___x_748_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_748_, 0, v___x_744_);
lean_ctor_set_uint8(v___x_748_, 1, v___x_744_);
lean_ctor_set_uint8(v___x_748_, 2, v___x_744_);
lean_ctor_set_uint8(v___x_748_, 3, v___x_744_);
lean_ctor_set_uint8(v___x_748_, 4, v___x_744_);
lean_ctor_set_uint8(v___x_748_, 5, v___x_657_);
lean_ctor_set_uint8(v___x_748_, 6, v___x_657_);
lean_ctor_set_uint8(v___x_748_, 7, v___x_744_);
lean_ctor_set_uint8(v___x_748_, 8, v___x_657_);
lean_ctor_set_uint8(v___x_748_, 9, v___x_745_);
lean_ctor_set_uint8(v___x_748_, 10, v___x_746_);
lean_ctor_set_uint8(v___x_748_, 11, v___x_657_);
lean_ctor_set_uint8(v___x_748_, 12, v___x_657_);
lean_ctor_set_uint8(v___x_748_, 13, v___x_657_);
lean_ctor_set_uint8(v___x_748_, 14, v___x_747_);
lean_ctor_set_uint8(v___x_748_, 15, v___x_657_);
lean_ctor_set_uint8(v___x_748_, 16, v___x_657_);
lean_ctor_set_uint8(v___x_748_, 17, v___x_657_);
lean_ctor_set_uint8(v___x_748_, 18, v___x_657_);
lean_ctor_set_uint8(v___x_748_, 19, v___x_744_);
v___x_749_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_748_);
v___x_750_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set_uint64(v___x_750_, sizeof(void*)*1, v___x_749_);
v___x_751_ = lean_unsigned_to_nat(0u);
v___x_752_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__10, &l_Lean_Compiler_LCNF_toDecl___closed__10_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__10);
v___x_753_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__11));
v___x_754_ = lean_box(0);
v___x_755_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_755_, 0, v___x_750_);
lean_ctor_set(v___x_755_, 1, v___x_600_);
lean_ctor_set(v___x_755_, 2, v___x_752_);
lean_ctor_set(v___x_755_, 3, v___x_753_);
lean_ctor_set(v___x_755_, 4, v___x_754_);
lean_ctor_set(v___x_755_, 5, v___x_751_);
lean_ctor_set(v___x_755_, 6, v___x_754_);
lean_ctor_set_uint8(v___x_755_, sizeof(void*)*7, v___x_744_);
lean_ctor_set_uint8(v___x_755_, sizeof(void*)*7 + 1, v___x_744_);
lean_ctor_set_uint8(v___x_755_, sizeof(void*)*7 + 2, v___x_744_);
lean_ctor_set_uint8(v___x_755_, sizeof(void*)*7 + 3, v___x_658_);
v___x_756_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__16, &l_Lean_Compiler_LCNF_toDecl___closed__16_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__16);
v___x_757_ = lean_st_mk_ref(v___x_756_);
v___x_758_ = l_Lean_Compiler_LCNF_toLCNFType(v___x_743_, v___x_755_, v___x_757_, v_a_492_, v_a_493_);
lean_dec_ref_known(v___x_755_, 7);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc_n(v_a_759_, 2);
lean_dec_ref_known(v___x_758_, 1);
v___x_760_ = lean_st_ref_get(v___x_757_);
lean_dec(v___x_757_);
lean_dec(v___x_760_);
v___x_761_ = l_Lean_Compiler_LCNF_toDecl___lam__0(v_a_759_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_774_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_774_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_774_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_774_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
v___x_766_ = l_Lean_ConstantInfo_levelParams(v_val_605_);
lean_dec(v_val_605_);
v___x_767_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_767_, 0, v___y_602_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
lean_ctor_set(v___x_767_, 2, v_a_759_);
lean_ctor_set(v___x_767_, 3, v_a_762_);
v___x_768_ = lean_unbox(v_a_607_);
lean_dec(v_a_607_);
lean_ctor_set_uint8(v___x_767_, sizeof(void*)*4, v___x_768_);
v___x_769_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__21));
v___x_770_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_770_, 0, v___x_767_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
lean_ctor_set(v___x_770_, 2, v___x_610_);
lean_ctor_set_uint8(v___x_770_, sizeof(void*)*3, v___x_744_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_770_);
v___x_772_ = v___x_764_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_dec(v_a_759_);
lean_dec(v___x_610_);
lean_dec(v_a_607_);
lean_dec(v_val_605_);
lean_dec(v___y_602_);
v_a_775_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_761_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_761_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec(v___x_757_);
lean_dec(v___x_610_);
lean_dec(v_a_607_);
lean_dec(v_val_605_);
lean_dec(v___y_602_);
v_a_783_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_758_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_758_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
else
{
lean_object* v___x_791_; uint8_t v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec(v_a_604_);
v___x_791_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__18, &l_Lean_Compiler_LCNF_toDecl___closed__18_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__18);
v___x_792_ = 0;
v___x_793_ = l_Lean_MessageData_ofConstName(v___y_602_, v___x_792_);
v___x_794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_791_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__23, &l_Lean_Compiler_LCNF_toDecl___closed__23_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__23);
v___x_796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_794_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__3___redArg(v___x_796_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
return v___x_797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___boxed(lean_object* v_declName_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_Compiler_LCNF_toDecl(v_declName_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1(uint8_t v___x_807_, lean_object* v_inst_808_, lean_object* v_a_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_807_, v_a_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___boxed(lean_object* v___x_816_, lean_object* v_inst_817_, lean_object* v_a_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
uint8_t v___x_14865__boxed_824_; lean_object* v_res_825_; 
v___x_14865__boxed_824_ = lean_unbox(v___x_816_);
v_res_825_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1(v___x_14865__boxed_824_, v_inst_817_, v_a_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4(uint8_t v___x_826_, size_t v_sz_827_, size_t v_i_828_, lean_object* v_bs_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___x_826_, v_sz_827_, v_i_828_, v_bs_829_, v___y_831_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___boxed(lean_object* v___x_836_, lean_object* v_sz_837_, lean_object* v_i_838_, lean_object* v_bs_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
uint8_t v___x_14888__boxed_845_; size_t v_sz_boxed_846_; size_t v_i_boxed_847_; lean_object* v_res_848_; 
v___x_14888__boxed_845_ = lean_unbox(v___x_836_);
v_sz_boxed_846_ = lean_unbox_usize(v_sz_837_);
lean_dec(v_sz_837_);
v_i_boxed_847_ = lean_unbox_usize(v_i_838_);
lean_dec(v_i_838_);
v_res_848_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4(v___x_14888__boxed_845_, v_sz_boxed_846_, v_i_boxed_847_, v_bs_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
return v_res_848_;
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
