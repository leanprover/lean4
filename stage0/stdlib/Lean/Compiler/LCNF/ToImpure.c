// Lean compiler output
// Module: Lean.Compiler.LCNF.ToImpure
// Imports: import Lean.Compiler.LCNF.ToImpureType public import Lean.Compiler.LCNF.PassManager import Lean.Compiler.LCNF.PhaseExt import Init.Data.Format.Macro
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
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_toImpureType(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addParam(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isVoid(lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_liftIOCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftBaseIOEIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___aux__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedCode_default__1(uint8_t);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addLetDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFVarImp___redArg(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_getCtorLayout(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_nameToImpureType(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CtorInfo_type(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default(uint8_t);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tagged_return"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(42, 116, 83, 63, 133, 144, 27, 22)}};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "mark extern definition to always return tagged values"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "taggedReturnAttr"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(217, 168, 64, 69, 229, 21, 118, 230)}};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__1_value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__3_value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__4_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ToImpure"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__4_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(104, 151, 203, 144, 27, 18, 236, 68)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(65, 46, 141, 239, 133, 91, 141, 199)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__7_value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(228, 234, 69, 211, 145, 232, 229, 254)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__8_value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(78, 187, 249, 147, 190, 91, 90, 40)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__9_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__9_value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(183, 4, 28, 224, 230, 52, 114, 252)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__10_value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(243, 95, 219, 231, 93, 109, 209, 250)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__11 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__11_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 150, .m_capacity = 150, .m_length = 149, .m_data = "Marks an extern definition to be guaranteed to always return tagged values.\nThis information is used to optimize reference counting in the compiler.\n"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__12 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__12_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__4_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__7_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__8_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_liftIOCore___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__9_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftBaseIOEIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__10_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__11 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__11_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftT___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__12 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__12_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__12_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__11_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__13 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__13_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__13_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__10_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__14 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__14_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__14_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__9_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__15 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__15_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__15_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__8_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__16 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__16_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftTOfMonadLift___redArg___lam__0, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__16_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__7_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__17 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__17_value;
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_get___boxed, .m_arity = 5, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__17_value)} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__18 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lcErased"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0_value),LEAN_SCALAR_PTR_LITERAL(171, 218, 234, 194, 194, 57, 75, 5)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__4_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__5_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "lcVoid"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__7_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__7_value),LEAN_SCALAR_PTR_LITERAL(68, 180, 59, 167, 252, 217, 37, 174)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__8_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Compiler.LCNF.ToImpure"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "_private.Lean.Compiler.LCNF.ToImpure.0.Lean.Compiler.LCNF.lowerResultType.resultTypeForArity"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "invalid arity"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__2_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lowerResultType(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lowerResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tobj"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(25, 168, 138, 20, 203, 141, 233, 12)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tagged"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__3_value),LEAN_SCALAR_PTR_LITERAL(167, 57, 252, 162, 142, 133, 51, 193)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__4_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "obj"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__6_value),LEAN_SCALAR_PTR_LITERAL(240, 235, 44, 74, 242, 121, 239, 90)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__9_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__9_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__12 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__12_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__12_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__15 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__15_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__15_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__18 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__18_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__18_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__19 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__19_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0;
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1;
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "projection of non-structure type"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "_private.Lean.Compiler.LCNF.ToImpure.0.Lean.Compiler.LCNF.lowerLet"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "overap"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "reference to unbound name"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "ToImpure: unexpected use of noncomputable declaration `"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__5_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "`; please report this issue"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__7_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__7_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9;
static const lean_array_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "code generator does not support recursor `"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__10_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__10_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "` yet, consider using 'match ... with' and/or structural recursion"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__12 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__12_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__12_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 38, .m_data = "all local functions should be λ-lifted"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "_private.Lean.Compiler.LCNF.ToImpure.0.Lean.Compiler.LCNF.Code.toImpure"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2;
static const lean_array_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "assertion violation: c.alts.size == 1\n      "};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "assertion violation: ctorName == info.ctorName\n      "};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "assertion violation: info.fieldIdx < ps.size\n      "};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "mismatched fields and params"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 76, .m_capacity = 76, .m_length = 75, .m_data = "_private.Lean.Compiler.LCNF.ToImpure.0.Lean.Compiler.LCNF.Alt.toImpure.loop"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Error while compiling function '"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "': @[tagged_return] is only valid for extern declarations"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "@[tagged_return] on function '"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "' with scalar return type "};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_toImpure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_toImpure___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_toImpure___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_toImpure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toImpure"};
static const lean_object* l_Lean_Compiler_LCNF_toImpure___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__1_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_toImpure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(136, 181, 13, 187, 73, 36, 105, 247)}};
static const lean_object* l_Lean_Compiler_LCNF_toImpure___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_toImpure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__2_value),((lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 2, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_toImpure___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_toImpure = (const lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(198, 36, 7, 136, 133, 159, 176, 55)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__10_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 198, 164, 214, 24, 238, 231, 213)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 168, 178, 247, 202, 119, 73, 243)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(202, 77, 105, 21, 218, 121, 239, 197)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 184, 169, 248, 178, 143, 79, 195)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 14, 162, 97, 10, 113, 167, 163)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(88, 160, 236, 105, 16, 144, 54, 23)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)(((size_t)(6355896) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(233, 87, 80, 162, 250, 65, 116, 159)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 254, 170, 235, 80, 165, 179, 171)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 19, 111, 73, 147, 106, 206, 64)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(135, 181, 11, 188, 89, 247, 207, 91)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_box(0);
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed(lean_object* v_x_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(v_x_7_, v___y_8_, v___y_9_);
lean_dec(v___y_9_);
lean_dec_ref(v___y_8_);
lean_dec(v_x_7_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___f_27_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_28_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_29_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_30_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_31_ = 0;
v___x_32_ = lean_box(2);
v___x_33_ = l_Lean_registerTagAttribute(v___x_28_, v___x_29_, v___f_27_, v___x_30_, v___x_31_, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed(lean_object* v_a_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_();
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1(){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_70_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__11));
v___x_71_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__12));
v___x_72_ = l_Lean_addBuiltinDocString(v___x_70_, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___boxed(lean_object* v_a_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1();
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0(lean_object* v_____do__lift_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_subst_82_; lean_object* v___x_83_; 
v_subst_82_ = lean_ctor_get(v_____do__lift_75_, 0);
lean_inc_ref(v_subst_82_);
v___x_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_83_, 0, v_subst_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0___boxed(lean_object* v_____do__lift_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0(v_____do__lift_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
lean_dec_ref(v_____do__lift_84_);
return v_res_91_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_instMonadEIO(lean_box(0));
return v___x_92_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0);
v___x_94_ = l_StateRefT_x27_instMonad___redArg(v___x_93_);
return v___x_94_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue(void){
_start:
{
lean_object* v___x_123_; lean_object* v_toApplicative_124_; lean_object* v_toFunctor_125_; lean_object* v_toSeq_126_; lean_object* v_toSeqLeft_127_; lean_object* v_toSeqRight_128_; lean_object* v___f_129_; lean_object* v___f_130_; lean_object* v___f_131_; lean_object* v___f_132_; lean_object* v___x_133_; lean_object* v___f_134_; lean_object* v___f_135_; lean_object* v___f_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v_toApplicative_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_170_; 
v___x_123_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1);
v_toApplicative_124_ = lean_ctor_get(v___x_123_, 0);
v_toFunctor_125_ = lean_ctor_get(v_toApplicative_124_, 0);
v_toSeq_126_ = lean_ctor_get(v_toApplicative_124_, 2);
v_toSeqLeft_127_ = lean_ctor_get(v_toApplicative_124_, 3);
v_toSeqRight_128_ = lean_ctor_get(v_toApplicative_124_, 4);
v___f_129_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2));
v___f_130_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3));
lean_inc_ref_n(v_toFunctor_125_, 2);
v___f_131_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_131_, 0, v_toFunctor_125_);
v___f_132_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_132_, 0, v_toFunctor_125_);
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v___f_131_);
lean_ctor_set(v___x_133_, 1, v___f_132_);
lean_inc(v_toSeqRight_128_);
v___f_134_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_134_, 0, v_toSeqRight_128_);
lean_inc(v_toSeqLeft_127_);
v___f_135_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_135_, 0, v_toSeqLeft_127_);
lean_inc(v_toSeq_126_);
v___f_136_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_136_, 0, v_toSeq_126_);
v___x_137_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_137_, 0, v___x_133_);
lean_ctor_set(v___x_137_, 1, v___f_129_);
lean_ctor_set(v___x_137_, 2, v___f_136_);
lean_ctor_set(v___x_137_, 3, v___f_135_);
lean_ctor_set(v___x_137_, 4, v___f_134_);
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v___f_130_);
v___x_139_ = l_StateRefT_x27_instMonad___redArg(v___x_138_);
v_toApplicative_140_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_170_ == 0)
{
lean_object* v_unused_171_; 
v_unused_171_ = lean_ctor_get(v___x_139_, 1);
lean_dec(v_unused_171_);
v___x_142_ = v___x_139_;
v_isShared_143_ = v_isSharedCheck_170_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_toApplicative_140_);
lean_dec(v___x_139_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_170_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v_toFunctor_144_; lean_object* v_toSeq_145_; lean_object* v_toSeqLeft_146_; lean_object* v_toSeqRight_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_168_; 
v_toFunctor_144_ = lean_ctor_get(v_toApplicative_140_, 0);
v_toSeq_145_ = lean_ctor_get(v_toApplicative_140_, 2);
v_toSeqLeft_146_ = lean_ctor_get(v_toApplicative_140_, 3);
v_toSeqRight_147_ = lean_ctor_get(v_toApplicative_140_, 4);
v_isSharedCheck_168_ = !lean_is_exclusive(v_toApplicative_140_);
if (v_isSharedCheck_168_ == 0)
{
lean_object* v_unused_169_; 
v_unused_169_ = lean_ctor_get(v_toApplicative_140_, 1);
lean_dec(v_unused_169_);
v___x_149_ = v_toApplicative_140_;
v_isShared_150_ = v_isSharedCheck_168_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_toSeqRight_147_);
lean_inc(v_toSeqLeft_146_);
lean_inc(v_toSeq_145_);
lean_inc(v_toFunctor_144_);
lean_dec(v_toApplicative_140_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_168_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___f_151_; lean_object* v___f_152_; lean_object* v___f_153_; lean_object* v___f_154_; lean_object* v___f_155_; lean_object* v___x_156_; lean_object* v___f_157_; lean_object* v___f_158_; lean_object* v___f_159_; lean_object* v___x_161_; 
v___f_151_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__4));
v___f_152_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5));
v___f_153_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6));
lean_inc_ref(v_toFunctor_144_);
v___f_154_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_154_, 0, v_toFunctor_144_);
v___f_155_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_155_, 0, v_toFunctor_144_);
v___x_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_156_, 0, v___f_154_);
lean_ctor_set(v___x_156_, 1, v___f_155_);
v___f_157_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_157_, 0, v_toSeqRight_147_);
v___f_158_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_158_, 0, v_toSeqLeft_146_);
v___f_159_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_159_, 0, v_toSeq_145_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 4, v___f_157_);
lean_ctor_set(v___x_149_, 3, v___f_158_);
lean_ctor_set(v___x_149_, 2, v___f_159_);
lean_ctor_set(v___x_149_, 1, v___f_152_);
lean_ctor_set(v___x_149_, 0, v___x_156_);
v___x_161_ = v___x_149_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v___f_152_);
lean_ctor_set(v_reuseFailAlloc_167_, 2, v___f_159_);
lean_ctor_set(v_reuseFailAlloc_167_, 3, v___f_158_);
lean_ctor_set(v_reuseFailAlloc_167_, 4, v___f_157_);
v___x_161_ = v_reuseFailAlloc_167_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
lean_object* v___x_163_; 
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 1, v___f_153_);
lean_ctor_set(v___x_142_, 0, v___x_161_);
v___x_163_ = v___x_142_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v___f_153_);
v___x_163_ = v_reuseFailAlloc_166_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__18));
v___x_165_ = lean_alloc_closure((void*)(l_StateRefT_x27_instMonad___aux__13___boxed), 9, 8);
lean_closure_set(v___x_165_, 0, lean_box(0));
lean_closure_set(v___x_165_, 1, lean_box(0));
lean_closure_set(v___x_165_, 2, lean_box(0));
lean_closure_set(v___x_165_, 3, v___x_163_);
lean_closure_set(v___x_165_, 4, lean_box(0));
lean_closure_set(v___x_165_, 5, lean_box(0));
lean_closure_set(v___x_165_, 6, v___x_164_);
lean_closure_set(v___x_165_, 7, v___f_151_);
return v___x_165_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0(lean_object* v_f_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v___x_179_; lean_object* v_subst_180_; lean_object* v_jpParamMask_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_192_; 
v___x_179_ = lean_st_ref_take(v___y_173_);
v_subst_180_ = lean_ctor_get(v___x_179_, 0);
v_jpParamMask_181_ = lean_ctor_get(v___x_179_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_192_ == 0)
{
v___x_183_ = v___x_179_;
v_isShared_184_ = v_isSharedCheck_192_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_jpParamMask_181_);
lean_inc(v_subst_180_);
lean_dec(v___x_179_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_192_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_185_ = lean_apply_1(v_f_172_, v_subst_180_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_185_);
v___x_187_ = v___x_183_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_jpParamMask_181_);
v___x_187_ = v_reuseFailAlloc_191_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = lean_st_ref_set(v___y_173_, v___x_187_);
v___x_189_ = lean_box(0);
v___x_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
return v___x_190_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0___boxed(lean_object* v_f_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0(v_f_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(lean_object* v_a_203_, lean_object* v_b_204_, lean_object* v_x_205_){
_start:
{
if (lean_obj_tag(v_x_205_) == 0)
{
lean_dec(v_b_204_);
lean_dec(v_a_203_);
return v_x_205_;
}
else
{
lean_object* v_key_206_; lean_object* v_value_207_; lean_object* v_tail_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_220_; 
v_key_206_ = lean_ctor_get(v_x_205_, 0);
v_value_207_ = lean_ctor_get(v_x_205_, 1);
v_tail_208_ = lean_ctor_get(v_x_205_, 2);
v_isSharedCheck_220_ = !lean_is_exclusive(v_x_205_);
if (v_isSharedCheck_220_ == 0)
{
v___x_210_ = v_x_205_;
v_isShared_211_ = v_isSharedCheck_220_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_tail_208_);
lean_inc(v_value_207_);
lean_inc(v_key_206_);
lean_dec(v_x_205_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_220_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
uint8_t v___x_212_; 
v___x_212_ = l_Lean_instBEqFVarId_beq(v_key_206_, v_a_203_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_213_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_203_, v_b_204_, v_tail_208_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 2, v___x_213_);
v___x_215_ = v___x_210_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_key_206_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_value_207_);
lean_ctor_set(v_reuseFailAlloc_216_, 2, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
else
{
lean_object* v___x_218_; 
lean_dec(v_value_207_);
lean_dec(v_key_206_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v_b_204_);
lean_ctor_set(v___x_210_, 0, v_a_203_);
v___x_218_ = v___x_210_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_203_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_b_204_);
lean_ctor_set(v_reuseFailAlloc_219_, 2, v_tail_208_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_221_, lean_object* v_x_222_){
_start:
{
if (lean_obj_tag(v_x_222_) == 0)
{
return v_x_221_;
}
else
{
lean_object* v_key_223_; lean_object* v_value_224_; lean_object* v_tail_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_248_; 
v_key_223_ = lean_ctor_get(v_x_222_, 0);
v_value_224_ = lean_ctor_get(v_x_222_, 1);
v_tail_225_ = lean_ctor_get(v_x_222_, 2);
v_isSharedCheck_248_ = !lean_is_exclusive(v_x_222_);
if (v_isSharedCheck_248_ == 0)
{
v___x_227_ = v_x_222_;
v_isShared_228_ = v_isSharedCheck_248_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_tail_225_);
lean_inc(v_value_224_);
lean_inc(v_key_223_);
lean_dec(v_x_222_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_248_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; uint64_t v___x_230_; uint64_t v___x_231_; uint64_t v___x_232_; uint64_t v_fold_233_; uint64_t v___x_234_; uint64_t v___x_235_; uint64_t v___x_236_; size_t v___x_237_; size_t v___x_238_; size_t v___x_239_; size_t v___x_240_; size_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_229_ = lean_array_get_size(v_x_221_);
v___x_230_ = l_Lean_instHashableFVarId_hash(v_key_223_);
v___x_231_ = 32ULL;
v___x_232_ = lean_uint64_shift_right(v___x_230_, v___x_231_);
v_fold_233_ = lean_uint64_xor(v___x_230_, v___x_232_);
v___x_234_ = 16ULL;
v___x_235_ = lean_uint64_shift_right(v_fold_233_, v___x_234_);
v___x_236_ = lean_uint64_xor(v_fold_233_, v___x_235_);
v___x_237_ = lean_uint64_to_usize(v___x_236_);
v___x_238_ = lean_usize_of_nat(v___x_229_);
v___x_239_ = ((size_t)1ULL);
v___x_240_ = lean_usize_sub(v___x_238_, v___x_239_);
v___x_241_ = lean_usize_land(v___x_237_, v___x_240_);
v___x_242_ = lean_array_uget_borrowed(v_x_221_, v___x_241_);
lean_inc(v___x_242_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 2, v___x_242_);
v___x_244_ = v___x_227_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_key_223_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_value_224_);
lean_ctor_set(v_reuseFailAlloc_247_, 2, v___x_242_);
v___x_244_ = v_reuseFailAlloc_247_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; 
v___x_245_ = lean_array_uset(v_x_221_, v___x_241_, v___x_244_);
v_x_221_ = v___x_245_;
v_x_222_ = v_tail_225_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(lean_object* v_i_249_, lean_object* v_source_250_, lean_object* v_target_251_){
_start:
{
lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_252_ = lean_array_get_size(v_source_250_);
v___x_253_ = lean_nat_dec_lt(v_i_249_, v___x_252_);
if (v___x_253_ == 0)
{
lean_dec_ref(v_source_250_);
lean_dec(v_i_249_);
return v_target_251_;
}
else
{
lean_object* v_es_254_; lean_object* v___x_255_; lean_object* v_source_256_; lean_object* v_target_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v_es_254_ = lean_array_fget(v_source_250_, v_i_249_);
v___x_255_ = lean_box(0);
v_source_256_ = lean_array_fset(v_source_250_, v_i_249_, v___x_255_);
v_target_257_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(v_target_251_, v_es_254_);
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_259_ = lean_nat_add(v_i_249_, v___x_258_);
lean_dec(v_i_249_);
v_i_249_ = v___x_259_;
v_source_250_ = v_source_256_;
v_target_251_ = v_target_257_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(lean_object* v_data_261_){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v_nbuckets_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_262_ = lean_array_get_size(v_data_261_);
v___x_263_ = lean_unsigned_to_nat(2u);
v_nbuckets_264_ = lean_nat_mul(v___x_262_, v___x_263_);
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = lean_box(0);
v___x_267_ = lean_mk_array(v_nbuckets_264_, v___x_266_);
v___x_268_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(v___x_265_, v_data_261_, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(lean_object* v_a_269_, lean_object* v_x_270_){
_start:
{
if (lean_obj_tag(v_x_270_) == 0)
{
uint8_t v___x_271_; 
v___x_271_ = 0;
return v___x_271_;
}
else
{
lean_object* v_key_272_; lean_object* v_tail_273_; uint8_t v___x_274_; 
v_key_272_ = lean_ctor_get(v_x_270_, 0);
v_tail_273_ = lean_ctor_get(v_x_270_, 2);
v___x_274_ = l_Lean_instBEqFVarId_beq(v_key_272_, v_a_269_);
if (v___x_274_ == 0)
{
v_x_270_ = v_tail_273_;
goto _start;
}
else
{
return v___x_274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg___boxed(lean_object* v_a_276_, lean_object* v_x_277_){
_start:
{
uint8_t v_res_278_; lean_object* v_r_279_; 
v_res_278_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_276_, v_x_277_);
lean_dec(v_x_277_);
lean_dec(v_a_276_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(lean_object* v_m_280_, lean_object* v_a_281_, lean_object* v_b_282_){
_start:
{
lean_object* v_size_283_; lean_object* v_buckets_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_327_; 
v_size_283_ = lean_ctor_get(v_m_280_, 0);
v_buckets_284_ = lean_ctor_get(v_m_280_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v_m_280_);
if (v_isSharedCheck_327_ == 0)
{
v___x_286_ = v_m_280_;
v_isShared_287_ = v_isSharedCheck_327_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_buckets_284_);
lean_inc(v_size_283_);
lean_dec(v_m_280_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_327_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; uint64_t v___x_291_; uint64_t v_fold_292_; uint64_t v___x_293_; uint64_t v___x_294_; uint64_t v___x_295_; size_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; lean_object* v_bkt_301_; uint8_t v___x_302_; 
v___x_288_ = lean_array_get_size(v_buckets_284_);
v___x_289_ = l_Lean_instHashableFVarId_hash(v_a_281_);
v___x_290_ = 32ULL;
v___x_291_ = lean_uint64_shift_right(v___x_289_, v___x_290_);
v_fold_292_ = lean_uint64_xor(v___x_289_, v___x_291_);
v___x_293_ = 16ULL;
v___x_294_ = lean_uint64_shift_right(v_fold_292_, v___x_293_);
v___x_295_ = lean_uint64_xor(v_fold_292_, v___x_294_);
v___x_296_ = lean_uint64_to_usize(v___x_295_);
v___x_297_ = lean_usize_of_nat(v___x_288_);
v___x_298_ = ((size_t)1ULL);
v___x_299_ = lean_usize_sub(v___x_297_, v___x_298_);
v___x_300_ = lean_usize_land(v___x_296_, v___x_299_);
v_bkt_301_ = lean_array_uget_borrowed(v_buckets_284_, v___x_300_);
v___x_302_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_281_, v_bkt_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v_size_x27_304_; lean_object* v___x_305_; lean_object* v_buckets_x27_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_303_ = lean_unsigned_to_nat(1u);
v_size_x27_304_ = lean_nat_add(v_size_283_, v___x_303_);
lean_dec(v_size_283_);
lean_inc(v_bkt_301_);
v___x_305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_305_, 0, v_a_281_);
lean_ctor_set(v___x_305_, 1, v_b_282_);
lean_ctor_set(v___x_305_, 2, v_bkt_301_);
v_buckets_x27_306_ = lean_array_uset(v_buckets_284_, v___x_300_, v___x_305_);
v___x_307_ = lean_unsigned_to_nat(4u);
v___x_308_ = lean_nat_mul(v_size_x27_304_, v___x_307_);
v___x_309_ = lean_unsigned_to_nat(3u);
v___x_310_ = lean_nat_div(v___x_308_, v___x_309_);
lean_dec(v___x_308_);
v___x_311_ = lean_array_get_size(v_buckets_x27_306_);
v___x_312_ = lean_nat_dec_le(v___x_310_, v___x_311_);
lean_dec(v___x_310_);
if (v___x_312_ == 0)
{
lean_object* v_val_313_; lean_object* v___x_315_; 
v_val_313_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(v_buckets_x27_306_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 1, v_val_313_);
lean_ctor_set(v___x_286_, 0, v_size_x27_304_);
v___x_315_ = v___x_286_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_size_x27_304_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_val_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
else
{
lean_object* v___x_318_; 
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 1, v_buckets_x27_306_);
lean_ctor_set(v___x_286_, 0, v_size_x27_304_);
v___x_318_ = v___x_286_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_size_x27_304_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_buckets_x27_306_);
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
lean_object* v___x_320_; lean_object* v_buckets_x27_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
lean_inc(v_bkt_301_);
v___x_320_ = lean_box(0);
v_buckets_x27_321_ = lean_array_uset(v_buckets_284_, v___x_300_, v___x_320_);
v___x_322_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_281_, v_b_282_, v_bkt_301_);
v___x_323_ = lean_array_uset(v_buckets_x27_321_, v___x_300_, v___x_322_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 1, v___x_323_);
v___x_325_ = v___x_286_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_size_283_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(lean_object* v_p_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_fvarId_334_; lean_object* v_binderName_335_; lean_object* v_type_336_; uint8_t v_borrow_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_393_; 
v_fvarId_334_ = lean_ctor_get(v_p_328_, 0);
v_binderName_335_ = lean_ctor_get(v_p_328_, 1);
v_type_336_ = lean_ctor_get(v_p_328_, 2);
v_borrow_337_ = lean_ctor_get_uint8(v_p_328_, sizeof(void*)*3);
v_isSharedCheck_393_ = !lean_is_exclusive(v_p_328_);
if (v_isSharedCheck_393_ == 0)
{
v___x_339_ = v_p_328_;
v_isShared_340_ = v_isSharedCheck_393_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_type_336_);
lean_inc(v_binderName_335_);
lean_inc(v_fvarId_334_);
lean_dec(v_p_328_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_393_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_Compiler_LCNF_toImpureType(v_type_336_, v_a_331_, v_a_332_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_384_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_384_ == 0)
{
v___x_344_ = v___x_341_;
v_isShared_345_ = v_isSharedCheck_384_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_384_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___y_347_; uint8_t v___y_368_; uint8_t v___x_382_; 
v___x_382_ = l_Lean_Expr_isVoid(v_a_342_);
if (v___x_382_ == 0)
{
uint8_t v___x_383_; 
v___x_383_ = l_Lean_Expr_isErased(v_a_342_);
v___y_368_ = v___x_383_;
goto v___jp_367_;
}
else
{
v___y_368_ = v___x_382_;
goto v___jp_367_;
}
v___jp_346_:
{
lean_object* v___x_348_; lean_object* v_lctx_349_; lean_object* v_nextIdx_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_366_; 
v___x_348_ = lean_st_ref_take(v___y_347_);
v_lctx_349_ = lean_ctor_get(v___x_348_, 0);
v_nextIdx_350_ = lean_ctor_get(v___x_348_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_366_ == 0)
{
v___x_352_ = v___x_348_;
v_isShared_353_ = v_isSharedCheck_366_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_nextIdx_350_);
lean_inc(v_lctx_349_);
lean_dec(v___x_348_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_366_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
uint8_t v___x_354_; lean_object* v___x_356_; 
v___x_354_ = 1;
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 2, v_a_342_);
v___x_356_ = v___x_339_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_fvarId_334_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_binderName_335_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_a_342_);
lean_ctor_set_uint8(v_reuseFailAlloc_365_, sizeof(void*)*3, v_borrow_337_);
v___x_356_ = v_reuseFailAlloc_365_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_357_; lean_object* v___x_359_; 
lean_inc_ref(v___x_356_);
v___x_357_ = l_Lean_Compiler_LCNF_LCtx_addParam(v___x_354_, v_lctx_349_, v___x_356_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_357_);
v___x_359_ = v___x_352_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_357_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_nextIdx_350_);
v___x_359_ = v_reuseFailAlloc_364_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_360_ = lean_st_ref_set(v___y_347_, v___x_359_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_356_);
v___x_362_ = v___x_344_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_356_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
v___jp_367_:
{
if (v___y_368_ == 0)
{
v___y_347_ = v_a_330_;
goto v___jp_346_;
}
else
{
lean_object* v___x_369_; lean_object* v_subst_370_; lean_object* v_jpParamMask_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_381_; 
v___x_369_ = lean_st_ref_take(v_a_329_);
v_subst_370_ = lean_ctor_get(v___x_369_, 0);
v_jpParamMask_371_ = lean_ctor_get(v___x_369_, 1);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_381_ == 0)
{
v___x_373_ = v___x_369_;
v_isShared_374_ = v_isSharedCheck_381_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_jpParamMask_371_);
lean_inc(v_subst_370_);
lean_dec(v___x_369_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_381_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_375_ = lean_box(0);
lean_inc(v_fvarId_334_);
v___x_376_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_370_, v_fvarId_334_, v___x_375_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_376_);
v___x_378_ = v___x_373_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_jpParamMask_371_);
v___x_378_ = v_reuseFailAlloc_380_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_379_; 
v___x_379_ = lean_st_ref_set(v_a_329_, v___x_378_);
v___y_347_ = v_a_330_;
goto v___jp_346_;
}
}
}
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_del_object(v___x_339_);
lean_dec(v_binderName_335_);
lean_dec(v_fvarId_334_);
v_a_385_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_341_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_341_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg___boxed(lean_object* v_p_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_p_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
lean_dec(v_a_396_);
lean_dec(v_a_395_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(lean_object* v_p_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_p_401_, v_a_402_, v_a_404_, v_a_405_, v_a_406_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___boxed(lean_object* v_p_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(v_p_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0(lean_object* v_00_u03b2_417_, lean_object* v_m_418_, lean_object* v_a_419_, lean_object* v_b_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_m_418_, v_a_419_, v_b_420_);
return v___x_421_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(lean_object* v_00_u03b2_422_, lean_object* v_a_423_, lean_object* v_x_424_){
_start:
{
uint8_t v___x_425_; 
v___x_425_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_423_, v_x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___boxed(lean_object* v_00_u03b2_426_, lean_object* v_a_427_, lean_object* v_x_428_){
_start:
{
uint8_t v_res_429_; lean_object* v_r_430_; 
v_res_429_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(v_00_u03b2_426_, v_a_427_, v_x_428_);
lean_dec(v_x_428_);
lean_dec(v_a_427_);
v_r_430_ = lean_box(v_res_429_);
return v_r_430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1(lean_object* v_00_u03b2_431_, lean_object* v_data_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(v_data_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2(lean_object* v_00_u03b2_434_, lean_object* v_a_435_, lean_object* v_b_436_, lean_object* v_x_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_435_, v_b_436_, v_x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_439_, lean_object* v_i_440_, lean_object* v_source_441_, lean_object* v_target_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(v_i_440_, v_source_441_, v_target_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_444_, lean_object* v_x_445_, lean_object* v_x_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(v_x_445_, v_x_446_);
return v___x_447_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_451_ = lean_box(0);
v___x_452_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1));
v___x_453_ = l_Lean_Expr_const___override(v___x_452_, v___x_451_);
return v___x_453_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2);
v___x_455_ = lean_box(1);
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v___x_454_);
return v___x_456_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = lean_box(0);
v___x_461_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__5));
v___x_462_ = l_Lean_Expr_const___override(v___x_461_, v___x_460_);
return v___x_462_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9(void){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = lean_box(0);
v___x_467_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__8));
v___x_468_ = l_Lean_Expr_const___override(v___x_467_, v___x_466_);
return v___x_468_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9);
v___x_470_ = lean_box(1);
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v___x_469_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(lean_object* v_base_472_, lean_object* v_ctorInfo_473_, lean_object* v_field_474_){
_start:
{
switch(lean_obj_tag(v_field_474_))
{
case 0:
{
lean_object* v___x_475_; 
lean_dec(v_base_472_);
v___x_475_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3);
return v___x_475_;
}
case 1:
{
lean_object* v_i_476_; lean_object* v_type_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_485_; 
v_i_476_ = lean_ctor_get(v_field_474_, 0);
v_type_477_ = lean_ctor_get(v_field_474_, 1);
v_isSharedCheck_485_ = !lean_is_exclusive(v_field_474_);
if (v_isSharedCheck_485_ == 0)
{
v___x_479_ = v_field_474_;
v_isShared_480_ = v_isSharedCheck_485_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_type_477_);
lean_inc(v_i_476_);
lean_dec(v_field_474_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_485_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set_tag(v___x_479_, 6);
lean_ctor_set(v___x_479_, 1, v_base_472_);
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_i_476_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_base_472_);
v___x_482_ = v_reuseFailAlloc_484_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_483_; 
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v_type_477_);
return v___x_483_;
}
}
}
case 2:
{
lean_object* v_i_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_i_486_ = lean_ctor_get(v_field_474_, 0);
lean_inc(v_i_486_);
lean_dec_ref(v_field_474_);
v___x_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_487_, 0, v_i_486_);
lean_ctor_set(v___x_487_, 1, v_base_472_);
v___x_488_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
return v___x_489_;
}
case 3:
{
lean_object* v_offset_490_; lean_object* v_type_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_502_; 
v_offset_490_ = lean_ctor_get(v_field_474_, 1);
v_type_491_ = lean_ctor_get(v_field_474_, 2);
v_isSharedCheck_502_ = !lean_is_exclusive(v_field_474_);
if (v_isSharedCheck_502_ == 0)
{
lean_object* v_unused_503_; 
v_unused_503_ = lean_ctor_get(v_field_474_, 0);
lean_dec(v_unused_503_);
v___x_493_ = v_field_474_;
v_isShared_494_ = v_isSharedCheck_502_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_type_491_);
lean_inc(v_offset_490_);
lean_dec(v_field_474_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_502_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v_size_495_; lean_object* v_usize_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
v_size_495_ = lean_ctor_get(v_ctorInfo_473_, 2);
v_usize_496_ = lean_ctor_get(v_ctorInfo_473_, 3);
v___x_497_ = lean_nat_add(v_size_495_, v_usize_496_);
if (v_isShared_494_ == 0)
{
lean_ctor_set_tag(v___x_493_, 8);
lean_ctor_set(v___x_493_, 2, v_base_472_);
lean_ctor_set(v___x_493_, 0, v___x_497_);
v___x_499_ = v___x_493_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_offset_490_);
lean_ctor_set(v_reuseFailAlloc_501_, 2, v_base_472_);
v___x_499_ = v_reuseFailAlloc_501_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; 
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
lean_ctor_set(v___x_500_, 1, v_type_491_);
return v___x_500_;
}
}
}
default: 
{
lean_object* v___x_504_; 
lean_dec(v_base_472_);
v___x_504_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10);
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___boxed(lean_object* v_base_505_, lean_object* v_ctorInfo_506_, lean_object* v_field_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_base_505_, v_ctorInfo_506_, v_field_507_);
lean_dec_ref(v_ctorInfo_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(lean_object* v_arg_509_, lean_object* v_a_510_){
_start:
{
lean_object* v___x_512_; lean_object* v_subst_513_; uint8_t v___x_514_; uint8_t v___x_515_; lean_object* v___x_516_; 
v___x_512_ = lean_st_ref_get(v_a_510_);
v_subst_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc_ref(v_subst_513_);
lean_dec(v___x_512_);
v___x_514_ = 0;
v___x_515_ = 1;
v___x_516_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v___x_514_, v_subst_513_, v_arg_509_, v___x_515_);
lean_dec_ref(v_subst_513_);
if (lean_obj_tag(v___x_516_) == 1)
{
lean_object* v_fvarId_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_525_; 
v_fvarId_517_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_525_ == 0)
{
v___x_519_ = v___x_516_;
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_fvarId_517_);
lean_dec(v___x_516_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_525_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_fvarId_517_);
v___x_522_ = v_reuseFailAlloc_524_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; 
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec(v___x_516_);
v___x_526_ = lean_box(0);
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg___boxed(lean_object* v_arg_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_arg_528_, v_a_529_);
lean_dec(v_a_529_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(lean_object* v_arg_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_arg_532_, v_a_533_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___boxed(lean_object* v_arg_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(v_arg_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec(v_a_541_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity_spec__0(lean_object* v_msg_548_){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = l_Lean_instInhabitedExpr;
v___x_550_ = lean_panic_fn_borrowed(v___x_549_, v_msg_548_);
return v___x_550_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_554_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__2));
v___x_555_ = lean_unsigned_to_nat(11u);
v___x_556_ = lean_unsigned_to_nat(83u);
v___x_557_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__1));
v___x_558_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_559_ = l_mkPanicMessageWithDecl(v___x_558_, v___x_557_, v___x_556_, v___x_555_, v___x_554_);
return v___x_559_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_560_ = lean_box(0);
v___x_561_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1));
v___x_562_ = l_Lean_mkConst(v___x_561_, v___x_560_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(lean_object* v_type_563_, lean_object* v_arity_564_){
_start:
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = lean_nat_dec_eq(v_arity_564_, v___x_568_);
if (v___x_569_ == 0)
{
switch(lean_obj_tag(v_type_563_))
{
case 7:
{
lean_object* v_body_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_body_570_ = lean_ctor_get(v_type_563_, 2);
v___x_571_ = lean_unsigned_to_nat(1u);
v___x_572_ = lean_nat_sub(v_arity_564_, v___x_571_);
lean_dec(v_arity_564_);
v_type_563_ = v_body_570_;
v_arity_564_ = v___x_572_;
goto _start;
}
case 4:
{
lean_object* v_declName_574_; 
lean_dec(v_arity_564_);
v_declName_574_ = lean_ctor_get(v_type_563_, 0);
if (lean_obj_tag(v_declName_574_) == 1)
{
lean_object* v_pre_575_; 
v_pre_575_ = lean_ctor_get(v_declName_574_, 0);
if (lean_obj_tag(v_pre_575_) == 0)
{
lean_object* v_str_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v_str_576_ = lean_ctor_get(v_declName_574_, 1);
v___x_577_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0));
v___x_578_ = lean_string_dec_eq(v_str_576_, v___x_577_);
if (v___x_578_ == 0)
{
goto v___jp_565_;
}
else
{
lean_object* v___x_579_; 
v___x_579_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4);
return v___x_579_;
}
}
else
{
goto v___jp_565_;
}
}
else
{
goto v___jp_565_;
}
}
default: 
{
lean_dec(v_arity_564_);
goto v___jp_565_;
}
}
}
else
{
lean_dec(v_arity_564_);
lean_inc_ref(v_type_563_);
return v_type_563_;
}
v___jp_565_:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3);
v___x_567_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity_spec__0(v___x_566_);
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___boxed(lean_object* v_type_580_, lean_object* v_arity_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(v_type_580_, v_arity_581_);
lean_dec_ref(v_type_580_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lowerResultType(lean_object* v_type_583_, lean_object* v_arity_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(v_type_583_, v_arity_584_);
v___x_589_ = l_Lean_Compiler_LCNF_toImpureType(v___x_588_, v_a_585_, v_a_586_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lowerResultType___boxed(lean_object* v_type_590_, lean_object* v_arity_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_590_, v_arity_591_, v_a_592_, v_a_593_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec_ref(v_type_590_);
return v_res_595_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = lean_box(0);
v___x_600_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__1));
v___x_601_ = l_Lean_Expr_const___override(v___x_600_, v___x_599_);
return v___x_601_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = lean_box(0);
v___x_606_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__4));
v___x_607_ = l_Lean_Expr_const___override(v___x_606_, v___x_605_);
return v___x_607_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = lean_box(0);
v___x_612_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7));
v___x_613_ = l_Lean_Expr_const___override(v___x_612_, v___x_611_);
return v___x_613_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_617_ = lean_box(0);
v___x_618_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10));
v___x_619_ = l_Lean_Expr_const___override(v___x_618_, v___x_617_);
return v___x_619_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = lean_box(0);
v___x_624_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13));
v___x_625_ = l_Lean_Expr_const___override(v___x_624_, v___x_623_);
return v___x_625_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_629_ = lean_box(0);
v___x_630_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16));
v___x_631_ = l_Lean_Expr_const___override(v___x_630_, v___x_629_);
return v___x_631_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_635_ = lean_box(0);
v___x_636_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__19));
v___x_637_ = l_Lean_Expr_const___override(v___x_636_, v___x_635_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(lean_object* v_v_638_){
_start:
{
switch(lean_obj_tag(v_v_638_))
{
case 0:
{
lean_object* v_val_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_val_639_ = lean_ctor_get(v_v_638_, 0);
v___x_640_ = lean_cstr_to_nat("4294967296");
v___x_641_ = lean_nat_dec_lt(v_val_639_, v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
v___x_642_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2);
return v___x_642_;
}
else
{
lean_object* v___x_643_; 
v___x_643_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5);
return v___x_643_;
}
}
case 1:
{
lean_object* v___x_644_; 
v___x_644_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
return v___x_644_;
}
case 2:
{
lean_object* v___x_645_; 
v___x_645_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11);
return v___x_645_;
}
case 3:
{
lean_object* v___x_646_; 
v___x_646_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14);
return v___x_646_;
}
case 4:
{
lean_object* v___x_647_; 
v___x_647_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17);
return v___x_647_;
}
case 5:
{
lean_object* v___x_648_; 
v___x_648_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20);
return v___x_648_;
}
default: 
{
lean_object* v___x_649_; 
v___x_649_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6);
return v___x_649_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___boxed(lean_object* v_v_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(v_v_650_);
lean_dec_ref(v_v_650_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(lean_object* v_as_652_, size_t v_i_653_, size_t v_stop_654_, lean_object* v_b_655_){
_start:
{
lean_object* v___y_657_; uint8_t v___x_661_; 
v___x_661_ = lean_usize_dec_eq(v_i_653_, v_stop_654_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; lean_object* v_snd_663_; uint8_t v___x_664_; 
v___x_662_ = lean_array_uget_borrowed(v_as_652_, v_i_653_);
v_snd_663_ = lean_ctor_get(v___x_662_, 1);
v___x_664_ = lean_unbox(v_snd_663_);
if (v___x_664_ == 0)
{
v___y_657_ = v_b_655_;
goto v___jp_656_;
}
else
{
lean_object* v_fst_665_; lean_object* v___x_666_; 
v_fst_665_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_fst_665_);
v___x_666_ = lean_array_push(v_b_655_, v_fst_665_);
v___y_657_ = v___x_666_;
goto v___jp_656_;
}
}
else
{
return v_b_655_;
}
v___jp_656_:
{
size_t v___x_658_; size_t v___x_659_; 
v___x_658_ = ((size_t)1ULL);
v___x_659_ = lean_usize_add(v_i_653_, v___x_658_);
v_i_653_ = v___x_659_;
v_b_655_ = v___y_657_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4___boxed(lean_object* v_as_667_, lean_object* v_i_668_, lean_object* v_stop_669_, lean_object* v_b_670_){
_start:
{
size_t v_i_boxed_671_; size_t v_stop_boxed_672_; lean_object* v_res_673_; 
v_i_boxed_671_ = lean_unbox_usize(v_i_668_);
lean_dec(v_i_668_);
v_stop_boxed_672_ = lean_unbox_usize(v_stop_669_);
lean_dec(v_stop_669_);
v_res_673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v_as_667_, v_i_boxed_671_, v_stop_boxed_672_, v_b_670_);
lean_dec_ref(v_as_667_);
return v_res_673_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0(void){
_start:
{
uint8_t v___x_674_; lean_object* v___x_675_; 
v___x_674_ = 1;
v___x_675_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(lean_object* v_msg_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___x_683_; lean_object* v_toApplicative_684_; lean_object* v_toFunctor_685_; lean_object* v_toSeq_686_; lean_object* v_toSeqLeft_687_; lean_object* v_toSeqRight_688_; lean_object* v___f_689_; lean_object* v___f_690_; lean_object* v___f_691_; lean_object* v___f_692_; lean_object* v___x_693_; lean_object* v___f_694_; lean_object* v___f_695_; lean_object* v___f_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v_toApplicative_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_732_; 
v___x_683_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1);
v_toApplicative_684_ = lean_ctor_get(v___x_683_, 0);
v_toFunctor_685_ = lean_ctor_get(v_toApplicative_684_, 0);
v_toSeq_686_ = lean_ctor_get(v_toApplicative_684_, 2);
v_toSeqLeft_687_ = lean_ctor_get(v_toApplicative_684_, 3);
v_toSeqRight_688_ = lean_ctor_get(v_toApplicative_684_, 4);
v___f_689_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2));
v___f_690_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3));
lean_inc_ref_n(v_toFunctor_685_, 2);
v___f_691_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_691_, 0, v_toFunctor_685_);
v___f_692_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_692_, 0, v_toFunctor_685_);
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v___f_691_);
lean_ctor_set(v___x_693_, 1, v___f_692_);
lean_inc(v_toSeqRight_688_);
v___f_694_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_694_, 0, v_toSeqRight_688_);
lean_inc(v_toSeqLeft_687_);
v___f_695_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_695_, 0, v_toSeqLeft_687_);
lean_inc(v_toSeq_686_);
v___f_696_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_696_, 0, v_toSeq_686_);
v___x_697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_697_, 0, v___x_693_);
lean_ctor_set(v___x_697_, 1, v___f_689_);
lean_ctor_set(v___x_697_, 2, v___f_696_);
lean_ctor_set(v___x_697_, 3, v___f_695_);
lean_ctor_set(v___x_697_, 4, v___f_694_);
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v___f_690_);
v___x_699_ = l_StateRefT_x27_instMonad___redArg(v___x_698_);
v_toApplicative_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; 
v_unused_733_ = lean_ctor_get(v___x_699_, 1);
lean_dec(v_unused_733_);
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_732_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_toApplicative_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_732_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v_toFunctor_704_; lean_object* v_toSeq_705_; lean_object* v_toSeqLeft_706_; lean_object* v_toSeqRight_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_730_; 
v_toFunctor_704_ = lean_ctor_get(v_toApplicative_700_, 0);
v_toSeq_705_ = lean_ctor_get(v_toApplicative_700_, 2);
v_toSeqLeft_706_ = lean_ctor_get(v_toApplicative_700_, 3);
v_toSeqRight_707_ = lean_ctor_get(v_toApplicative_700_, 4);
v_isSharedCheck_730_ = !lean_is_exclusive(v_toApplicative_700_);
if (v_isSharedCheck_730_ == 0)
{
lean_object* v_unused_731_; 
v_unused_731_ = lean_ctor_get(v_toApplicative_700_, 1);
lean_dec(v_unused_731_);
v___x_709_ = v_toApplicative_700_;
v_isShared_710_ = v_isSharedCheck_730_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_toSeqRight_707_);
lean_inc(v_toSeqLeft_706_);
lean_inc(v_toSeq_705_);
lean_inc(v_toFunctor_704_);
lean_dec(v_toApplicative_700_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_730_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___f_711_; lean_object* v___f_712_; lean_object* v___f_713_; lean_object* v___f_714_; lean_object* v___x_715_; lean_object* v___f_716_; lean_object* v___f_717_; lean_object* v___f_718_; lean_object* v___x_720_; 
v___f_711_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5));
v___f_712_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6));
lean_inc_ref(v_toFunctor_704_);
v___f_713_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_713_, 0, v_toFunctor_704_);
v___f_714_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_714_, 0, v_toFunctor_704_);
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v___f_713_);
lean_ctor_set(v___x_715_, 1, v___f_714_);
v___f_716_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_716_, 0, v_toSeqRight_707_);
v___f_717_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_717_, 0, v_toSeqLeft_706_);
v___f_718_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_718_, 0, v_toSeq_705_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 4, v___f_716_);
lean_ctor_set(v___x_709_, 3, v___f_717_);
lean_ctor_set(v___x_709_, 2, v___f_718_);
lean_ctor_set(v___x_709_, 1, v___f_711_);
lean_ctor_set(v___x_709_, 0, v___x_715_);
v___x_720_ = v___x_709_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v___f_711_);
lean_ctor_set(v_reuseFailAlloc_729_, 2, v___f_718_);
lean_ctor_set(v_reuseFailAlloc_729_, 3, v___f_717_);
lean_ctor_set(v_reuseFailAlloc_729_, 4, v___f_716_);
v___x_720_ = v_reuseFailAlloc_729_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_722_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v___f_712_);
lean_ctor_set(v___x_702_, 0, v___x_720_);
v___x_722_ = v___x_702_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v___f_712_);
v___x_722_ = v_reuseFailAlloc_728_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_38241__overap_726_; lean_object* v___x_727_; 
v___x_723_ = l_StateRefT_x27_instMonad___redArg(v___x_722_);
v___x_724_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0);
v___x_725_ = l_instInhabitedOfMonad___redArg(v___x_723_, v___x_724_);
v___x_38241__overap_726_ = lean_panic_fn_borrowed(v___x_725_, v_msg_676_);
lean_dec(v___x_725_);
lean_inc(v___y_681_);
lean_inc_ref(v___y_680_);
lean_inc(v___y_679_);
lean_inc_ref(v___y_678_);
lean_inc(v___y_677_);
v___x_727_ = lean_apply_6(v___x_38241__overap_726_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, lean_box(0));
return v___x_727_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___boxed(lean_object* v_msg_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v_msg_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
return v_res_741_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0(void){
_start:
{
uint8_t v___x_742_; lean_object* v___x_743_; 
v___x_742_ = 0;
v___x_743_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(lean_object* v_upperBound_744_, lean_object* v_params_745_, lean_object* v___x_746_, lean_object* v_discr_747_, lean_object* v_a_748_, lean_object* v_b_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_a_753_; uint8_t v___x_757_; 
v___x_757_ = lean_nat_dec_lt(v_a_748_, v_upperBound_744_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; 
lean_dec(v_a_748_);
lean_dec(v_discr_747_);
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v_b_749_);
return v___x_758_;
}
else
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_759_ = lean_box(0);
v___x_760_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0);
v___x_761_ = lean_array_get_borrowed(v___x_760_, v_params_745_, v_a_748_);
v___x_762_ = lean_nat_dec_eq(v_a_748_, v___x_746_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v_fvarId_764_; lean_object* v_subst_765_; lean_object* v_jpParamMask_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_776_; 
v___x_763_ = lean_st_ref_take(v___y_750_);
v_fvarId_764_ = lean_ctor_get(v___x_761_, 0);
v_subst_765_ = lean_ctor_get(v___x_763_, 0);
v_jpParamMask_766_ = lean_ctor_get(v___x_763_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_776_ == 0)
{
v___x_768_ = v___x_763_;
v_isShared_769_ = v_isSharedCheck_776_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_jpParamMask_766_);
lean_inc(v_subst_765_);
lean_dec(v___x_763_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_776_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_770_ = lean_box(0);
lean_inc(v_fvarId_764_);
v___x_771_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_765_, v_fvarId_764_, v___x_770_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_771_);
v___x_773_ = v___x_768_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_jpParamMask_766_);
v___x_773_ = v_reuseFailAlloc_775_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_774_; 
v___x_774_ = lean_st_ref_set(v___y_750_, v___x_773_);
v_a_753_ = v___x_759_;
goto v___jp_752_;
}
}
}
else
{
lean_object* v___x_777_; lean_object* v_fvarId_778_; lean_object* v_subst_779_; lean_object* v_jpParamMask_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_790_; 
v___x_777_ = lean_st_ref_take(v___y_750_);
v_fvarId_778_ = lean_ctor_get(v___x_761_, 0);
v_subst_779_ = lean_ctor_get(v___x_777_, 0);
v_jpParamMask_780_ = lean_ctor_get(v___x_777_, 1);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_790_ == 0)
{
v___x_782_ = v___x_777_;
v_isShared_783_ = v_isSharedCheck_790_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_jpParamMask_780_);
lean_inc(v_subst_779_);
lean_dec(v___x_777_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_790_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
lean_inc(v_discr_747_);
v___x_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_784_, 0, v_discr_747_);
lean_inc(v_fvarId_778_);
v___x_785_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_779_, v_fvarId_778_, v___x_784_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_785_);
v___x_787_ = v___x_782_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_jpParamMask_780_);
v___x_787_ = v_reuseFailAlloc_789_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_788_; 
v___x_788_ = lean_st_ref_set(v___y_750_, v___x_787_);
v_a_753_ = v___x_759_;
goto v___jp_752_;
}
}
}
}
v___jp_752_:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_unsigned_to_nat(1u);
v___x_755_ = lean_nat_add(v_a_748_, v___x_754_);
lean_dec(v_a_748_);
v_a_748_ = v___x_755_;
v_b_749_ = v_a_753_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___boxed(lean_object* v_upperBound_791_, lean_object* v_params_792_, lean_object* v___x_793_, lean_object* v_discr_794_, lean_object* v_a_795_, lean_object* v_b_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v_upperBound_791_, v_params_792_, v___x_793_, v_discr_794_, v_a_795_, v_b_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec(v___x_793_);
lean_dec_ref(v_params_792_);
lean_dec(v_upperBound_791_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(size_t v_sz_800_, size_t v_i_801_, lean_object* v_bs_802_){
_start:
{
uint8_t v___x_803_; 
v___x_803_ = lean_usize_dec_lt(v_i_801_, v_sz_800_);
if (v___x_803_ == 0)
{
return v_bs_802_;
}
else
{
lean_object* v_v_804_; lean_object* v_type_805_; lean_object* v___x_806_; lean_object* v_bs_x27_807_; uint8_t v___y_809_; uint8_t v___y_816_; uint8_t v___x_818_; 
v_v_804_ = lean_array_uget_borrowed(v_bs_802_, v_i_801_);
v_type_805_ = lean_ctor_get(v_v_804_, 2);
lean_inc_ref(v_type_805_);
v___x_806_ = lean_unsigned_to_nat(0u);
v_bs_x27_807_ = lean_array_uset(v_bs_802_, v_i_801_, v___x_806_);
v___x_818_ = l_Lean_Expr_isVoid(v_type_805_);
if (v___x_818_ == 0)
{
uint8_t v___x_819_; 
v___x_819_ = l_Lean_Expr_isErased(v_type_805_);
lean_dec_ref(v_type_805_);
v___y_816_ = v___x_819_;
goto v___jp_815_;
}
else
{
lean_dec_ref(v_type_805_);
v___y_816_ = v___x_818_;
goto v___jp_815_;
}
v___jp_808_:
{
size_t v___x_810_; size_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_810_ = ((size_t)1ULL);
v___x_811_ = lean_usize_add(v_i_801_, v___x_810_);
v___x_812_ = lean_box(v___y_809_);
v___x_813_ = lean_array_uset(v_bs_x27_807_, v_i_801_, v___x_812_);
v_i_801_ = v___x_811_;
v_bs_802_ = v___x_813_;
goto _start;
}
v___jp_815_:
{
if (v___y_816_ == 0)
{
v___y_809_ = v___x_803_;
goto v___jp_808_;
}
else
{
uint8_t v___x_817_; 
v___x_817_ = 0;
v___y_809_ = v___x_817_;
goto v___jp_808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3___boxed(lean_object* v_sz_820_, lean_object* v_i_821_, lean_object* v_bs_822_){
_start:
{
size_t v_sz_boxed_823_; size_t v_i_boxed_824_; lean_object* v_res_825_; 
v_sz_boxed_823_ = lean_unbox_usize(v_sz_820_);
lean_dec(v_sz_820_);
v_i_boxed_824_ = lean_unbox_usize(v_i_821_);
lean_dec(v_i_821_);
v_res_825_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(v_sz_boxed_823_, v_i_boxed_824_, v_bs_822_);
return v_res_825_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_826_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0);
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
return v___x_828_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1);
v___x_830_ = lean_unsigned_to_nat(0u);
v___x_831_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
lean_ctor_set(v___x_831_, 2, v___x_830_);
lean_ctor_set(v___x_831_, 3, v___x_829_);
lean_ctor_set(v___x_831_, 4, v___x_829_);
lean_ctor_set(v___x_831_, 5, v___x_829_);
lean_ctor_set(v___x_831_, 6, v___x_829_);
lean_ctor_set(v___x_831_, 7, v___x_829_);
lean_ctor_set(v___x_831_, 8, v___x_829_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(lean_object* v_msg_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_options_838_; lean_object* v_ref_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_options_838_ = lean_ctor_get(v___y_835_, 2);
v_ref_839_ = lean_ctor_get(v___y_835_, 5);
v___x_840_ = lean_st_ref_get(v___y_836_);
v___x_841_ = lean_st_ref_get(v___y_834_);
v___x_842_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_833_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_865_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_865_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_865_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_865_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v_env_847_; lean_object* v_lctx_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_863_; 
v_env_847_ = lean_ctor_get(v___x_840_, 0);
lean_inc_ref(v_env_847_);
lean_dec(v___x_840_);
v_lctx_848_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_863_ == 0)
{
lean_object* v_unused_864_; 
v_unused_864_ = lean_ctor_get(v___x_841_, 1);
lean_dec(v_unused_864_);
v___x_850_ = v___x_841_;
v_isShared_851_ = v_isSharedCheck_863_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_lctx_848_);
lean_dec(v___x_841_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_863_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
uint8_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_852_ = lean_unbox(v_a_843_);
lean_dec(v_a_843_);
v___x_853_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_848_, v___x_852_);
lean_dec_ref(v_lctx_848_);
v___x_854_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2);
lean_inc_ref(v_options_838_);
v___x_855_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_855_, 0, v_env_847_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
lean_ctor_set(v___x_855_, 2, v___x_853_);
lean_ctor_set(v___x_855_, 3, v_options_838_);
if (v_isShared_851_ == 0)
{
lean_ctor_set_tag(v___x_850_, 3);
lean_ctor_set(v___x_850_, 1, v_msg_832_);
lean_ctor_set(v___x_850_, 0, v___x_855_);
v___x_857_ = v___x_850_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v_msg_832_);
v___x_857_ = v_reuseFailAlloc_862_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; lean_object* v___x_860_; 
lean_inc(v_ref_839_);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v_ref_839_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
if (v_isShared_846_ == 0)
{
lean_ctor_set_tag(v___x_845_, 1);
lean_ctor_set(v___x_845_, 0, v___x_858_);
v___x_860_ = v___x_845_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec(v___x_841_);
lean_dec(v___x_840_);
lean_dec_ref(v_msg_832_);
v_a_866_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_842_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_842_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___boxed(lean_object* v_msg_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_msg_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(size_t v_sz_881_, size_t v_i_882_, lean_object* v_bs_883_, lean_object* v___y_884_){
_start:
{
uint8_t v___x_886_; 
v___x_886_ = lean_usize_dec_lt(v_i_882_, v_sz_881_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; 
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v_bs_883_);
return v___x_887_;
}
else
{
lean_object* v_v_888_; lean_object* v___x_889_; 
v_v_888_ = lean_array_uget_borrowed(v_bs_883_, v_i_882_);
lean_inc(v_v_888_);
v___x_889_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_v_888_, v___y_884_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_891_; lean_object* v_bs_x27_892_; size_t v___x_893_; size_t v___x_894_; lean_object* v___x_895_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref(v___x_889_);
v___x_891_ = lean_unsigned_to_nat(0u);
v_bs_x27_892_ = lean_array_uset(v_bs_883_, v_i_882_, v___x_891_);
v___x_893_ = ((size_t)1ULL);
v___x_894_ = lean_usize_add(v_i_882_, v___x_893_);
v___x_895_ = lean_array_uset(v_bs_x27_892_, v_i_882_, v_a_890_);
v_i_882_ = v___x_894_;
v_bs_883_ = v___x_895_;
goto _start;
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_dec_ref(v_bs_883_);
v_a_897_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_889_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_889_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg___boxed(lean_object* v_sz_905_, lean_object* v_i_906_, lean_object* v_bs_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
size_t v_sz_boxed_910_; size_t v_i_boxed_911_; lean_object* v_res_912_; 
v_sz_boxed_910_ = lean_unbox_usize(v_sz_905_);
lean_dec(v_sz_905_);
v_i_boxed_911_ = lean_unbox_usize(v_i_906_);
lean_dec(v_i_906_);
v_res_912_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_boxed_910_, v_i_boxed_911_, v_bs_907_, v___y_908_);
lean_dec(v___y_908_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(lean_object* v_upperBound_913_, lean_object* v_fieldInfo_914_, lean_object* v___x_915_, lean_object* v_a_916_, lean_object* v_b_917_){
_start:
{
lean_object* v_a_920_; uint8_t v___x_924_; 
v___x_924_ = lean_nat_dec_lt(v_a_916_, v_upperBound_913_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; 
lean_dec(v_a_916_);
v___x_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_925_, 0, v_b_917_);
return v___x_925_;
}
else
{
lean_object* v___x_926_; 
v___x_926_ = lean_array_fget_borrowed(v_fieldInfo_914_, v_a_916_);
switch(lean_obj_tag(v___x_926_))
{
case 1:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_927_ = lean_box(0);
v___x_928_ = lean_array_get_borrowed(v___x_927_, v___x_915_, v_a_916_);
lean_inc(v___x_928_);
v___x_929_ = lean_array_push(v_b_917_, v___x_928_);
v_a_920_ = v___x_929_;
goto v___jp_919_;
}
case 2:
{
v_a_920_ = v_b_917_;
goto v___jp_919_;
}
case 3:
{
v_a_920_ = v_b_917_;
goto v___jp_919_;
}
default: 
{
v_a_920_ = v_b_917_;
goto v___jp_919_;
}
}
}
v___jp_919_:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_unsigned_to_nat(1u);
v___x_922_ = lean_nat_add(v_a_916_, v___x_921_);
lean_dec(v_a_916_);
v_a_916_ = v___x_922_;
v_b_917_ = v_a_920_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___boxed(lean_object* v_upperBound_930_, lean_object* v_fieldInfo_931_, lean_object* v___x_932_, lean_object* v_a_933_, lean_object* v_b_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v_upperBound_930_, v_fieldInfo_931_, v___x_932_, v_a_933_, v_b_934_);
lean_dec_ref(v___x_932_);
lean_dec_ref(v_fieldInfo_931_);
lean_dec(v_upperBound_930_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(lean_object* v_as_937_, size_t v_i_938_, size_t v_stop_939_, lean_object* v_b_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_a_944_; uint8_t v___x_948_; 
v___x_948_ = lean_usize_dec_eq(v_i_938_, v_stop_939_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; lean_object* v_snd_950_; uint8_t v___x_951_; 
v___x_949_ = lean_array_uget_borrowed(v_as_937_, v_i_938_);
v_snd_950_ = lean_ctor_get(v___x_949_, 1);
v___x_951_ = lean_unbox(v_snd_950_);
if (v___x_951_ == 0)
{
v_a_944_ = v_b_940_;
goto v___jp_943_;
}
else
{
lean_object* v_fst_952_; lean_object* v___x_953_; 
v_fst_952_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_fst_952_);
v___x_953_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_fst_952_, v___y_941_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_955_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref(v___x_953_);
v___x_955_ = lean_array_push(v_b_940_, v_a_954_);
v_a_944_ = v___x_955_;
goto v___jp_943_;
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec_ref(v_b_940_);
v_a_956_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_953_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_953_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
else
{
lean_object* v___x_964_; 
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v_b_940_);
return v___x_964_;
}
v___jp_943_:
{
size_t v___x_945_; size_t v___x_946_; 
v___x_945_ = ((size_t)1ULL);
v___x_946_ = lean_usize_add(v_i_938_, v___x_945_);
v_i_938_ = v___x_946_;
v_b_940_ = v_a_944_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg___boxed(lean_object* v_as_965_, lean_object* v_i_966_, lean_object* v_stop_967_, lean_object* v_b_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
size_t v_i_boxed_971_; size_t v_stop_boxed_972_; lean_object* v_res_973_; 
v_i_boxed_971_ = lean_unbox_usize(v_i_966_);
lean_dec(v_i_966_);
v_stop_boxed_972_ = lean_unbox_usize(v_stop_967_);
lean_dec(v_stop_967_);
v_res_973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v_as_965_, v_i_boxed_971_, v_stop_boxed_972_, v_b_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v_as_965_);
return v_res_973_;
}
}
static lean_object* _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0(void){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Array_instInhabited(lean_box(0));
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17(lean_object* v_msg_975_){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = lean_obj_once(&l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0, &l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0_once, _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0);
v___x_977_ = lean_panic_fn_borrowed(v___x_976_, v_msg_975_);
return v___x_977_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_981_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__2));
v___x_982_ = lean_unsigned_to_nat(11u);
v___x_983_ = lean_unsigned_to_nat(163u);
v___x_984_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__1));
v___x_985_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__0));
v___x_986_ = l_mkPanicMessageWithDecl(v___x_985_, v___x_984_, v___x_983_, v___x_982_, v___x_981_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(lean_object* v_a_987_, lean_object* v_x_988_){
_start:
{
if (lean_obj_tag(v_x_988_) == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3);
v___x_990_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17(v___x_989_);
return v___x_990_;
}
else
{
lean_object* v_key_991_; lean_object* v_value_992_; lean_object* v_tail_993_; uint8_t v___x_994_; 
v_key_991_ = lean_ctor_get(v_x_988_, 0);
v_value_992_ = lean_ctor_get(v_x_988_, 1);
v_tail_993_ = lean_ctor_get(v_x_988_, 2);
v___x_994_ = l_Lean_instBEqFVarId_beq(v_key_991_, v_a_987_);
if (v___x_994_ == 0)
{
v_x_988_ = v_tail_993_;
goto _start;
}
else
{
lean_inc(v_value_992_);
return v_value_992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___boxed(lean_object* v_a_996_, lean_object* v_x_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(v_a_996_, v_x_997_);
lean_dec(v_x_997_);
lean_dec(v_a_996_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(lean_object* v_m_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_buckets_1001_; lean_object* v___x_1002_; uint64_t v___x_1003_; uint64_t v___x_1004_; uint64_t v___x_1005_; uint64_t v_fold_1006_; uint64_t v___x_1007_; uint64_t v___x_1008_; uint64_t v___x_1009_; size_t v___x_1010_; size_t v___x_1011_; size_t v___x_1012_; size_t v___x_1013_; size_t v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_buckets_1001_ = lean_ctor_get(v_m_999_, 1);
v___x_1002_ = lean_array_get_size(v_buckets_1001_);
v___x_1003_ = l_Lean_instHashableFVarId_hash(v_a_1000_);
v___x_1004_ = 32ULL;
v___x_1005_ = lean_uint64_shift_right(v___x_1003_, v___x_1004_);
v_fold_1006_ = lean_uint64_xor(v___x_1003_, v___x_1005_);
v___x_1007_ = 16ULL;
v___x_1008_ = lean_uint64_shift_right(v_fold_1006_, v___x_1007_);
v___x_1009_ = lean_uint64_xor(v_fold_1006_, v___x_1008_);
v___x_1010_ = lean_uint64_to_usize(v___x_1009_);
v___x_1011_ = lean_usize_of_nat(v___x_1002_);
v___x_1012_ = ((size_t)1ULL);
v___x_1013_ = lean_usize_sub(v___x_1011_, v___x_1012_);
v___x_1014_ = lean_usize_land(v___x_1010_, v___x_1013_);
v___x_1015_ = lean_array_uget_borrowed(v_buckets_1001_, v___x_1014_);
v___x_1016_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(v_a_1000_, v___x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___boxed(lean_object* v_m_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(v_m_1017_, v_a_1018_);
lean_dec(v_a_1018_);
lean_dec_ref(v_m_1017_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(size_t v_sz_1020_, size_t v_i_1021_, lean_object* v_bs_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
uint8_t v___x_1028_; 
v___x_1028_ = lean_usize_dec_lt(v_i_1021_, v_sz_1020_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v_bs_1022_);
return v___x_1029_;
}
else
{
lean_object* v_v_1030_; lean_object* v___x_1031_; 
v_v_1030_ = lean_array_uget_borrowed(v_bs_1022_, v_i_1021_);
lean_inc(v_v_1030_);
v___x_1031_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_v_1030_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1033_; lean_object* v_bs_x27_1034_; size_t v___x_1035_; size_t v___x_1036_; lean_object* v___x_1037_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref(v___x_1031_);
v___x_1033_ = lean_unsigned_to_nat(0u);
v_bs_x27_1034_ = lean_array_uset(v_bs_1022_, v_i_1021_, v___x_1033_);
v___x_1035_ = ((size_t)1ULL);
v___x_1036_ = lean_usize_add(v_i_1021_, v___x_1035_);
v___x_1037_ = lean_array_uset(v_bs_x27_1034_, v_i_1021_, v_a_1032_);
v_i_1021_ = v___x_1036_;
v_bs_1022_ = v___x_1037_;
goto _start;
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec_ref(v_bs_1022_);
v_a_1039_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1031_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1031_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg___boxed(lean_object* v_sz_1047_, lean_object* v_i_1048_, lean_object* v_bs_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
size_t v_sz_boxed_1055_; size_t v_i_boxed_1056_; lean_object* v_res_1057_; 
v_sz_boxed_1055_ = lean_unbox_usize(v_sz_1047_);
lean_dec(v_sz_1047_);
v_i_boxed_1056_ = lean_unbox_usize(v_i_1048_);
lean_dec(v_i_1048_);
v_res_1057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_boxed_1055_, v_i_boxed_1056_, v_bs_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec(v___y_1050_);
return v_res_1057_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1060_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1));
v___x_1061_ = lean_unsigned_to_nat(12u);
v___x_1062_ = lean_unsigned_to_nat(116u);
v___x_1063_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0));
v___x_1064_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1065_ = l_mkPanicMessageWithDecl(v___x_1064_, v___x_1063_, v___x_1062_, v___x_1061_, v___x_1060_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(lean_object* v_k_1066_, lean_object* v_decl_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v___x_1074_; lean_object* v_lctx_1075_; lean_object* v_nextIdx_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1096_; 
v___x_1074_ = lean_st_ref_take(v_a_1070_);
v_lctx_1075_ = lean_ctor_get(v___x_1074_, 0);
v_nextIdx_1076_ = lean_ctor_get(v___x_1074_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1078_ = v___x_1074_;
v_isShared_1079_ = v_isSharedCheck_1096_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_nextIdx_1076_);
lean_inc(v_lctx_1075_);
lean_dec(v___x_1074_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1096_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
uint8_t v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1080_ = 1;
lean_inc_ref(v_decl_1067_);
v___x_1081_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1080_, v_lctx_1075_, v_decl_1067_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1081_);
v___x_1083_ = v___x_1078_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_nextIdx_1076_);
v___x_1083_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_st_ref_set(v_a_1070_, v___x_1083_);
v___x_1085_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1066_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1094_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1094_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1094_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v_decl_1067_);
lean_ctor_set(v___x_1090_, 1, v_a_1086_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1090_);
v___x_1092_ = v___x_1088_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
else
{
lean_dec_ref(v_decl_1067_);
return v___x_1085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(lean_object* v_k_1097_, lean_object* v_fvarId_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v___x_1105_; lean_object* v_subst_1106_; lean_object* v_jpParamMask_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1118_; 
v___x_1105_ = lean_st_ref_take(v_a_1099_);
v_subst_1106_ = lean_ctor_get(v___x_1105_, 0);
v_jpParamMask_1107_ = lean_ctor_get(v___x_1105_, 1);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1109_ = v___x_1105_;
v_isShared_1110_ = v_isSharedCheck_1118_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_jpParamMask_1107_);
lean_inc(v_subst_1106_);
lean_dec(v___x_1105_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1118_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1111_ = lean_box(0);
v___x_1112_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1106_, v_fvarId_1098_, v___x_1111_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1112_);
v___x_1114_ = v___x_1109_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_jpParamMask_1107_);
v___x_1114_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = lean_st_ref_set(v_a_1099_, v___x_1114_);
v___x_1116_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1097_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_);
return v___x_1116_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(lean_object* v_decl_1120_, lean_object* v_k_1121_, lean_object* v_name_1122_, lean_object* v_numParams_1123_, lean_object* v_args_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v_fvarId_1131_; lean_object* v_binderName_1132_; lean_object* v_type_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1195_; 
v_fvarId_1131_ = lean_ctor_get(v_decl_1120_, 0);
v_binderName_1132_ = lean_ctor_get(v_decl_1120_, 1);
v_type_1133_ = lean_ctor_get(v_decl_1120_, 2);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_decl_1120_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; 
v_unused_1196_ = lean_ctor_get(v_decl_1120_, 3);
lean_dec(v_unused_1196_);
v___x_1135_ = v_decl_1120_;
v_isShared_1136_ = v_isSharedCheck_1195_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_type_1133_);
lean_inc(v_binderName_1132_);
lean_inc(v_fvarId_1131_);
lean_dec(v_decl_1120_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1195_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1133_, v_a_1128_, v_a_1129_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref(v___x_1137_);
v___x_1139_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1123_);
v___x_1140_ = l_Array_extract___redArg(v_args_1124_, v___x_1139_, v_numParams_1123_);
v___x_1141_ = 1;
v___x_1142_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0));
lean_inc(v_binderName_1132_);
v___x_1143_ = l_Lean_Name_str___override(v_binderName_1132_, v___x_1142_);
v___x_1144_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
v___x_1145_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_1145_, 0, v_name_1122_);
lean_ctor_set(v___x_1145_, 1, v___x_1140_);
v___x_1146_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1141_, v___x_1143_, v___x_1144_, v___x_1145_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v_fvarId_1148_; lean_object* v___x_1149_; lean_object* v_lctx_1150_; lean_object* v_nextIdx_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1178_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref(v___x_1146_);
v_fvarId_1148_ = lean_ctor_get(v_a_1147_, 0);
v___x_1149_ = lean_st_ref_take(v_a_1127_);
v_lctx_1150_ = lean_ctor_get(v___x_1149_, 0);
v_nextIdx_1151_ = lean_ctor_get(v___x_1149_, 1);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1153_ = v___x_1149_;
v_isShared_1154_ = v_isSharedCheck_1178_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_nextIdx_1151_);
lean_inc(v_lctx_1150_);
lean_dec(v___x_1149_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1178_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1155_ = lean_array_get_size(v_args_1124_);
v___x_1156_ = l_Array_extract___redArg(v_args_1124_, v_numParams_1123_, v___x_1155_);
lean_inc(v_fvarId_1148_);
v___x_1157_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1157_, 0, v_fvarId_1148_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v___x_1158_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_a_1138_);
lean_dec(v_a_1138_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 3, v___x_1157_);
lean_ctor_set(v___x_1135_, 2, v___x_1158_);
v___x_1160_ = v___x_1135_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_fvarId_1131_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_binderName_1132_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1177_, 3, v___x_1157_);
v___x_1160_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1161_; lean_object* v___x_1163_; 
lean_inc_ref(v___x_1160_);
v___x_1161_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1141_, v_lctx_1150_, v___x_1160_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1161_);
v___x_1163_ = v___x_1153_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_nextIdx_1151_);
v___x_1163_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_st_ref_set(v_a_1127_, v___x_1163_);
v___x_1165_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1121_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1175_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1168_ = v___x_1165_;
v_isShared_1169_ = v_isSharedCheck_1175_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1165_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1175_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1160_);
lean_ctor_set(v___x_1170_, 1, v_a_1166_);
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v_a_1147_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 0, v___x_1171_);
v___x_1173_ = v___x_1168_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
else
{
lean_dec_ref(v___x_1160_);
lean_dec(v_a_1147_);
return v___x_1165_;
}
}
}
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec(v_a_1138_);
lean_del_object(v___x_1135_);
lean_dec(v_binderName_1132_);
lean_dec(v_fvarId_1131_);
lean_dec(v_numParams_1123_);
lean_dec_ref(v_k_1121_);
v_a_1179_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1146_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1146_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_del_object(v___x_1135_);
lean_dec(v_binderName_1132_);
lean_dec(v_fvarId_1131_);
lean_dec(v_numParams_1123_);
lean_dec(v_name_1122_);
lean_dec_ref(v_k_1121_);
v_a_1187_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1137_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1137_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(lean_object* v_decl_1197_, lean_object* v_k_1198_, lean_object* v_name_1199_, lean_object* v_args_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v_fvarId_1207_; lean_object* v_binderName_1208_; lean_object* v_type_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1228_; 
v_fvarId_1207_ = lean_ctor_get(v_decl_1197_, 0);
v_binderName_1208_ = lean_ctor_get(v_decl_1197_, 1);
v_type_1209_ = lean_ctor_get(v_decl_1197_, 2);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_decl_1197_);
if (v_isSharedCheck_1228_ == 0)
{
lean_object* v_unused_1229_; 
v_unused_1229_ = lean_ctor_get(v_decl_1197_, 3);
lean_dec(v_unused_1229_);
v___x_1211_ = v_decl_1197_;
v_isShared_1212_ = v_isSharedCheck_1228_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_type_1209_);
lean_inc(v_binderName_1208_);
lean_inc(v_fvarId_1207_);
lean_dec(v_decl_1197_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1228_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1209_, v_a_1204_, v_a_1205_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
lean_dec_ref(v___x_1213_);
v___x_1215_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_1215_, 0, v_name_1199_);
lean_ctor_set(v___x_1215_, 1, v_args_1200_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 3, v___x_1215_);
lean_ctor_set(v___x_1211_, 2, v_a_1214_);
v___x_1217_ = v___x_1211_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_fvarId_1207_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_binderName_1208_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v_a_1214_);
lean_ctor_set(v_reuseFailAlloc_1219_, 3, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1218_; 
v___x_1218_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1198_, v___x_1217_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
return v___x_1218_;
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_del_object(v___x_1211_);
lean_dec(v_binderName_1208_);
lean_dec(v_fvarId_1207_);
lean_dec_ref(v_args_1200_);
lean_dec(v_name_1199_);
lean_dec_ref(v_k_1198_);
v_a_1220_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1213_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1213_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(lean_object* v_decl_1230_, lean_object* v_k_1231_, lean_object* v_name_1232_, lean_object* v_args_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v_fvarId_1240_; lean_object* v_binderName_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1251_; 
v_fvarId_1240_ = lean_ctor_get(v_decl_1230_, 0);
v_binderName_1241_ = lean_ctor_get(v_decl_1230_, 1);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_decl_1230_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; lean_object* v_unused_1253_; 
v_unused_1252_ = lean_ctor_get(v_decl_1230_, 3);
lean_dec(v_unused_1252_);
v_unused_1253_ = lean_ctor_get(v_decl_1230_, 2);
lean_dec(v_unused_1253_);
v___x_1243_ = v_decl_1230_;
v_isShared_1244_ = v_isSharedCheck_1251_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_binderName_1241_);
lean_inc(v_fvarId_1240_);
lean_dec(v_decl_1230_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1251_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1248_; 
v___x_1245_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
v___x_1246_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_name_1232_);
lean_ctor_set(v___x_1246_, 1, v_args_1233_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 3, v___x_1246_);
lean_ctor_set(v___x_1243_, 2, v___x_1245_);
v___x_1248_ = v___x_1243_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_fvarId_1240_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_binderName_1241_);
lean_ctor_set(v_reuseFailAlloc_1250_, 2, v___x_1245_);
lean_ctor_set(v_reuseFailAlloc_1250_, 3, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; 
v___x_1249_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1231_, v___x_1248_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_);
return v___x_1249_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(lean_object* v_decl_1254_, lean_object* v_k_1255_, lean_object* v_name_1256_, lean_object* v_numParams_1257_, lean_object* v_args_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
lean_object* v_numArgs_1265_; uint8_t v___x_1266_; 
v_numArgs_1265_ = lean_array_get_size(v_args_1258_);
v___x_1266_ = lean_nat_dec_lt(v_numArgs_1265_, v_numParams_1257_);
if (v___x_1266_ == 0)
{
uint8_t v___x_1267_; 
v___x_1267_ = lean_nat_dec_eq(v_numArgs_1265_, v_numParams_1257_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; 
v___x_1268_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(v_decl_1254_, v_k_1255_, v_name_1256_, v_numParams_1257_, v_args_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
lean_dec_ref(v_args_1258_);
return v___x_1268_;
}
else
{
lean_object* v___x_1269_; 
lean_dec(v_numParams_1257_);
v___x_1269_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_1254_, v_k_1255_, v_name_1256_, v_args_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
return v___x_1269_;
}
}
else
{
lean_object* v___x_1270_; 
lean_dec(v_numParams_1257_);
v___x_1270_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(v_decl_1254_, v_k_1255_, v_name_1256_, v_args_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
return v___x_1270_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1272_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3));
v___x_1273_ = lean_unsigned_to_nat(14u);
v___x_1274_ = lean_unsigned_to_nat(185u);
v___x_1275_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0));
v___x_1276_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1277_ = l_mkPanicMessageWithDecl(v___x_1276_, v___x_1275_, v___x_1274_, v___x_1273_, v___x_1272_);
return v___x_1277_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2);
v___x_1285_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(lean_object* v_decl_1294_, lean_object* v_k_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___x_1310_; lean_object* v_fvarId_1311_; lean_object* v_binderName_1312_; lean_object* v_type_1313_; lean_object* v_value_1314_; lean_object* v_subst_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1767_; 
v___x_1310_ = lean_st_ref_get(v_a_1296_);
v_fvarId_1311_ = lean_ctor_get(v_decl_1294_, 0);
v_binderName_1312_ = lean_ctor_get(v_decl_1294_, 1);
v_type_1313_ = lean_ctor_get(v_decl_1294_, 2);
v_value_1314_ = lean_ctor_get(v_decl_1294_, 3);
v_subst_1315_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1767_ == 0)
{
lean_object* v_unused_1768_; 
v_unused_1768_ = lean_ctor_get(v___x_1310_, 1);
lean_dec(v_unused_1768_);
v___x_1317_ = v___x_1310_;
v_isShared_1318_ = v_isSharedCheck_1767_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_subst_1315_);
lean_dec(v___x_1310_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1767_;
goto v_resetjp_1316_;
}
v___jp_1302_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2);
v___x_1309_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1308_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
return v___x_1309_;
}
v_resetjp_1316_:
{
uint8_t v___x_1319_; uint8_t v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = 0;
v___x_1320_ = 1;
lean_inc(v_value_1314_);
v___x_1321_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v___x_1319_, v_subst_1315_, v_value_1314_, v___x_1320_);
lean_dec_ref(v_subst_1315_);
switch(lean_obj_tag(v___x_1321_))
{
case 0:
{
lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1338_; 
lean_inc(v_binderName_1312_);
lean_inc(v_fvarId_1311_);
lean_del_object(v___x_1317_);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_decl_1294_);
if (v_isSharedCheck_1338_ == 0)
{
lean_object* v_unused_1339_; lean_object* v_unused_1340_; lean_object* v_unused_1341_; lean_object* v_unused_1342_; 
v_unused_1339_ = lean_ctor_get(v_decl_1294_, 3);
lean_dec(v_unused_1339_);
v_unused_1340_ = lean_ctor_get(v_decl_1294_, 2);
lean_dec(v_unused_1340_);
v_unused_1341_ = lean_ctor_get(v_decl_1294_, 1);
lean_dec(v_unused_1341_);
v_unused_1342_ = lean_ctor_get(v_decl_1294_, 0);
lean_dec(v_unused_1342_);
v___x_1323_ = v_decl_1294_;
v_isShared_1324_ = v_isSharedCheck_1338_;
goto v_resetjp_1322_;
}
else
{
lean_dec(v_decl_1294_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1338_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v_value_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1337_; 
v_value_1325_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1327_ = v___x_1321_;
v_isShared_1328_ = v_isSharedCheck_1337_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_value_1325_);
lean_dec(v___x_1321_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1337_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1329_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(v_value_1325_);
if (v_isShared_1328_ == 0)
{
v___x_1331_ = v___x_1327_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_value_1325_);
v___x_1331_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1333_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 3, v___x_1331_);
lean_ctor_set(v___x_1323_, 2, v___x_1329_);
v___x_1333_ = v___x_1323_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_fvarId_1311_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_binderName_1312_);
lean_ctor_set(v_reuseFailAlloc_1335_, 2, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1335_, 3, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1334_; 
v___x_1334_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1295_, v___x_1333_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1334_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1343_; 
lean_inc(v_fvarId_1311_);
lean_del_object(v___x_1317_);
lean_dec_ref(v_decl_1294_);
v___x_1343_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_1295_, v_fvarId_1311_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1343_;
}
case 2:
{
lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1446_; 
lean_inc(v_binderName_1312_);
lean_inc(v_fvarId_1311_);
lean_del_object(v___x_1317_);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_decl_1294_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; lean_object* v_unused_1448_; lean_object* v_unused_1449_; lean_object* v_unused_1450_; 
v_unused_1447_ = lean_ctor_get(v_decl_1294_, 3);
lean_dec(v_unused_1447_);
v_unused_1448_ = lean_ctor_get(v_decl_1294_, 2);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_decl_1294_, 1);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_decl_1294_, 0);
lean_dec(v_unused_1450_);
v___x_1345_ = v_decl_1294_;
v_isShared_1346_ = v_isSharedCheck_1446_;
goto v_resetjp_1344_;
}
else
{
lean_dec(v_decl_1294_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1446_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v_typeName_1347_; lean_object* v_idx_1348_; lean_object* v_struct_1349_; lean_object* v___x_1350_; 
v_typeName_1347_ = lean_ctor_get(v___x_1321_, 0);
lean_inc_n(v_typeName_1347_, 2);
v_idx_1348_ = lean_ctor_get(v___x_1321_, 1);
lean_inc(v_idx_1348_);
v_struct_1349_ = lean_ctor_get(v___x_1321_, 2);
lean_inc(v_struct_1349_);
lean_dec_ref(v___x_1321_);
v___x_1350_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_typeName_1347_, v_a_1299_, v_a_1300_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref(v___x_1350_);
if (lean_obj_tag(v_a_1351_) == 1)
{
lean_object* v_val_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1388_; 
lean_dec(v_typeName_1347_);
lean_del_object(v___x_1345_);
lean_dec(v_binderName_1312_);
v_val_1352_ = lean_ctor_get(v_a_1351_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v_a_1351_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1354_ = v_a_1351_;
v_isShared_1355_ = v_isSharedCheck_1388_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_val_1352_);
lean_dec(v_a_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1388_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v_fieldIdx_1356_; uint8_t v___x_1357_; 
v_fieldIdx_1356_ = lean_ctor_get(v_val_1352_, 2);
lean_inc(v_fieldIdx_1356_);
lean_dec(v_val_1352_);
v___x_1357_ = lean_nat_dec_eq(v_fieldIdx_1356_, v_idx_1348_);
lean_dec(v_idx_1348_);
lean_dec(v_fieldIdx_1356_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v_subst_1359_; lean_object* v_jpParamMask_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1371_; 
lean_del_object(v___x_1354_);
lean_dec(v_struct_1349_);
v___x_1358_ = lean_st_ref_take(v_a_1296_);
v_subst_1359_ = lean_ctor_get(v___x_1358_, 0);
v_jpParamMask_1360_ = lean_ctor_get(v___x_1358_, 1);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1362_ = v___x_1358_;
v_isShared_1363_ = v_isSharedCheck_1371_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_jpParamMask_1360_);
lean_inc(v_subst_1359_);
lean_dec(v___x_1358_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1371_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1364_ = lean_box(0);
v___x_1365_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1359_, v_fvarId_1311_, v___x_1364_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1365_);
v___x_1367_ = v___x_1362_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_jpParamMask_1360_);
v___x_1367_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_st_ref_set(v_a_1296_, v___x_1367_);
v___x_1369_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1369_;
}
}
}
else
{
lean_object* v___x_1372_; lean_object* v_subst_1373_; lean_object* v_jpParamMask_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1387_; 
v___x_1372_ = lean_st_ref_take(v_a_1296_);
v_subst_1373_ = lean_ctor_get(v___x_1372_, 0);
v_jpParamMask_1374_ = lean_ctor_get(v___x_1372_, 1);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1376_ = v___x_1372_;
v_isShared_1377_ = v_isSharedCheck_1387_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_jpParamMask_1374_);
lean_inc(v_subst_1373_);
lean_dec(v___x_1372_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1387_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v_struct_1349_);
v___x_1379_ = v___x_1354_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_struct_1349_);
v___x_1379_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v___x_1380_; lean_object* v___x_1382_; 
v___x_1380_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1373_, v_fvarId_1311_, v___x_1379_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 0, v___x_1380_);
v___x_1382_ = v___x_1376_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_jpParamMask_1374_);
v___x_1382_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = lean_st_ref_set(v_a_1296_, v___x_1382_);
v___x_1384_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1384_;
}
}
}
}
}
}
else
{
lean_object* v___x_1389_; lean_object* v_subst_1390_; lean_object* v___x_1391_; 
lean_dec(v_a_1351_);
v___x_1389_ = lean_st_ref_get(v_a_1296_);
v_subst_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc_ref(v_subst_1390_);
lean_dec(v___x_1389_);
v___x_1391_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1390_, v_struct_1349_, v___x_1320_);
lean_dec_ref(v_subst_1390_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_fvarId_1392_; lean_object* v___x_1393_; lean_object* v_env_1394_; uint8_t v___x_1395_; lean_object* v___x_1396_; 
v_fvarId_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_fvarId_1392_);
lean_dec_ref(v___x_1391_);
v___x_1393_ = lean_st_ref_get(v_a_1300_);
v_env_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc_ref(v_env_1394_);
lean_dec(v___x_1393_);
v___x_1395_ = 0;
v___x_1396_ = l_Lean_Environment_find_x3f(v_env_1394_, v_typeName_1347_, v___x_1395_);
if (lean_obj_tag(v___x_1396_) == 1)
{
lean_object* v_val_1397_; 
v_val_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_val_1397_);
lean_dec_ref(v___x_1396_);
if (lean_obj_tag(v_val_1397_) == 5)
{
lean_object* v_val_1398_; lean_object* v_ctors_1399_; 
v_val_1398_ = lean_ctor_get(v_val_1397_, 0);
lean_inc_ref(v_val_1398_);
lean_dec_ref(v_val_1397_);
v_ctors_1399_ = lean_ctor_get(v_val_1398_, 4);
lean_inc(v_ctors_1399_);
lean_dec_ref(v_val_1398_);
if (lean_obj_tag(v_ctors_1399_) == 1)
{
lean_object* v_tail_1400_; 
v_tail_1400_ = lean_ctor_get(v_ctors_1399_, 1);
if (lean_obj_tag(v_tail_1400_) == 0)
{
lean_object* v_head_1401_; lean_object* v___x_1402_; 
v_head_1401_ = lean_ctor_get(v_ctors_1399_, 0);
lean_inc(v_head_1401_);
lean_dec_ref(v_ctors_1399_);
v___x_1402_ = l_Lean_Compiler_LCNF_getCtorLayout(v_head_1401_, v_a_1299_, v_a_1300_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; lean_object* v_ctorInfo_1404_; lean_object* v_fieldInfo_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v_fst_1409_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref(v___x_1402_);
v_ctorInfo_1404_ = lean_ctor_get(v_a_1403_, 0);
lean_inc_ref(v_ctorInfo_1404_);
v_fieldInfo_1405_ = lean_ctor_get(v_a_1403_, 1);
lean_inc_ref(v_fieldInfo_1405_);
lean_dec(v_a_1403_);
v___x_1406_ = lean_box(0);
v___x_1407_ = lean_array_get(v___x_1406_, v_fieldInfo_1405_, v_idx_1348_);
lean_dec(v_idx_1348_);
lean_dec_ref(v_fieldInfo_1405_);
v___x_1408_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_fvarId_1392_, v_ctorInfo_1404_, v___x_1407_);
lean_dec_ref(v_ctorInfo_1404_);
v_fst_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_fst_1409_);
if (lean_obj_tag(v_fst_1409_) == 1)
{
lean_object* v___x_1410_; 
lean_dec_ref(v___x_1408_);
lean_del_object(v___x_1345_);
lean_dec(v_binderName_1312_);
v___x_1410_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_1295_, v_fvarId_1311_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1410_;
}
else
{
lean_object* v_snd_1411_; lean_object* v___x_1413_; 
v_snd_1411_ = lean_ctor_get(v___x_1408_, 1);
lean_inc(v_snd_1411_);
lean_dec_ref(v___x_1408_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 3, v_fst_1409_);
lean_ctor_set(v___x_1345_, 2, v_snd_1411_);
v___x_1413_ = v___x_1345_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_fvarId_1311_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_binderName_1312_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_snd_1411_);
lean_ctor_set(v_reuseFailAlloc_1415_, 3, v_fst_1409_);
v___x_1413_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1414_; 
v___x_1414_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1295_, v___x_1413_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1414_;
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec(v_fvarId_1392_);
lean_dec(v_idx_1348_);
lean_del_object(v___x_1345_);
lean_dec(v_binderName_1312_);
lean_dec(v_fvarId_1311_);
lean_dec_ref(v_k_1295_);
v_a_1416_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1402_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1402_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
else
{
lean_dec_ref(v_ctors_1399_);
lean_dec(v_fvarId_1392_);
lean_dec(v_idx_1348_);
lean_del_object(v___x_1345_);
lean_dec(v_binderName_1312_);
lean_dec(v_fvarId_1311_);
lean_dec_ref(v_k_1295_);
v___y_1303_ = v_a_1296_;
v___y_1304_ = v_a_1297_;
v___y_1305_ = v_a_1298_;
v___y_1306_ = v_a_1299_;
v___y_1307_ = v_a_1300_;
goto v___jp_1302_;
}
}
else
{
lean_dec(v_ctors_1399_);
lean_dec(v_fvarId_1392_);
lean_dec(v_idx_1348_);
lean_del_object(v___x_1345_);
lean_dec(v_binderName_1312_);
lean_dec(v_fvarId_1311_);
lean_dec_ref(v_k_1295_);
v___y_1303_ = v_a_1296_;
v___y_1304_ = v_a_1297_;
v___y_1305_ = v_a_1298_;
v___y_1306_ = v_a_1299_;
v___y_1307_ = v_a_1300_;
goto v___jp_1302_;
}
}
else
{
lean_dec(v_val_1397_);
lean_dec(v_fvarId_1392_);
lean_dec(v_idx_1348_);
lean_del_object(v___x_1345_);
lean_dec(v_binderName_1312_);
lean_dec(v_fvarId_1311_);
lean_dec_ref(v_k_1295_);
v___y_1303_ = v_a_1296_;
v___y_1304_ = v_a_1297_;
v___y_1305_ = v_a_1298_;
v___y_1306_ = v_a_1299_;
v___y_1307_ = v_a_1300_;
goto v___jp_1302_;
}
}
else
{
lean_dec(v___x_1396_);
lean_dec(v_fvarId_1392_);
lean_dec(v_idx_1348_);
lean_del_object(v___x_1345_);
lean_dec(v_binderName_1312_);
lean_dec(v_fvarId_1311_);
lean_dec_ref(v_k_1295_);
v___y_1303_ = v_a_1296_;
v___y_1304_ = v_a_1297_;
v___y_1305_ = v_a_1298_;
v___y_1306_ = v_a_1299_;
v___y_1307_ = v_a_1300_;
goto v___jp_1302_;
}
}
else
{
lean_object* v___x_1424_; lean_object* v_subst_1425_; lean_object* v_jpParamMask_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1437_; 
lean_dec(v_idx_1348_);
lean_dec(v_typeName_1347_);
lean_del_object(v___x_1345_);
lean_dec(v_binderName_1312_);
v___x_1424_ = lean_st_ref_take(v_a_1296_);
v_subst_1425_ = lean_ctor_get(v___x_1424_, 0);
v_jpParamMask_1426_ = lean_ctor_get(v___x_1424_, 1);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1428_ = v___x_1424_;
v_isShared_1429_ = v_isSharedCheck_1437_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_jpParamMask_1426_);
lean_inc(v_subst_1425_);
lean_dec(v___x_1424_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1437_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1430_ = lean_box(0);
v___x_1431_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1425_, v_fvarId_1311_, v___x_1430_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v___x_1431_);
v___x_1433_ = v___x_1428_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_jpParamMask_1426_);
v___x_1433_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_st_ref_set(v_a_1296_, v___x_1433_);
v___x_1435_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1435_;
}
}
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_dec(v_struct_1349_);
lean_dec(v_idx_1348_);
lean_dec(v_typeName_1347_);
lean_del_object(v___x_1345_);
lean_dec(v_binderName_1312_);
lean_dec(v_fvarId_1311_);
lean_dec_ref(v_k_1295_);
v_a_1438_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1350_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1350_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
case 3:
{
lean_object* v_declName_1451_; lean_object* v_args_1452_; size_t v_sz_1453_; size_t v___x_1454_; lean_object* v___x_1455_; 
v_declName_1451_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_declName_1451_);
v_args_1452_ = lean_ctor_get(v___x_1321_, 2);
lean_inc_ref_n(v_args_1452_, 2);
lean_dec_ref(v___x_1321_);
v_sz_1453_ = lean_array_size(v_args_1452_);
v___x_1454_ = ((size_t)0ULL);
v___x_1455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_1453_, v___x_1454_, v_args_1452_, v_a_1296_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1457_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref(v___x_1455_);
lean_inc(v_declName_1451_);
v___x_1457_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_1451_, v_a_1300_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref(v___x_1457_);
if (lean_obj_tag(v_a_1458_) == 1)
{
lean_object* v_val_1459_; lean_object* v_params_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec_ref(v_args_1452_);
lean_del_object(v___x_1317_);
v_val_1459_ = lean_ctor_get(v_a_1458_, 0);
lean_inc(v_val_1459_);
lean_dec_ref(v_a_1458_);
v_params_1460_ = lean_ctor_get(v_val_1459_, 3);
lean_inc_ref(v_params_1460_);
lean_dec(v_val_1459_);
v___x_1461_ = lean_array_get_size(v_params_1460_);
lean_dec_ref(v_params_1460_);
v___x_1462_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_1294_, v_k_1295_, v_declName_1451_, v___x_1461_, v_a_1456_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1462_;
}
else
{
lean_object* v___x_1463_; 
lean_dec(v_a_1458_);
lean_inc(v_declName_1451_);
v___x_1463_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_1451_, v_a_1300_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref(v___x_1463_);
if (lean_obj_tag(v_a_1464_) == 1)
{
lean_object* v_val_1465_; lean_object* v_toSignature_1466_; lean_object* v_params_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec_ref(v_args_1452_);
lean_del_object(v___x_1317_);
v_val_1465_ = lean_ctor_get(v_a_1464_, 0);
lean_inc(v_val_1465_);
lean_dec_ref(v_a_1464_);
v_toSignature_1466_ = lean_ctor_get(v_val_1465_, 0);
lean_inc_ref(v_toSignature_1466_);
lean_dec(v_val_1465_);
v_params_1467_ = lean_ctor_get(v_toSignature_1466_, 3);
lean_inc_ref(v_params_1467_);
lean_dec_ref(v_toSignature_1466_);
v___x_1468_ = lean_array_get_size(v_params_1467_);
lean_dec_ref(v_params_1467_);
v___x_1469_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_1294_, v_k_1295_, v_declName_1451_, v___x_1468_, v_a_1456_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1469_;
}
else
{
lean_object* v___x_1470_; lean_object* v_env_1471_; uint8_t v___x_1472_; lean_object* v___x_1473_; 
lean_dec(v_a_1464_);
v___x_1470_ = lean_st_ref_get(v_a_1300_);
v_env_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc_ref(v_env_1471_);
lean_dec(v___x_1470_);
v___x_1472_ = 0;
lean_inc(v_declName_1451_);
v___x_1473_ = l_Lean_Environment_find_x3f(v_env_1471_, v_declName_1451_, v___x_1472_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_dec(v_a_1456_);
lean_dec_ref(v_args_1452_);
lean_dec(v_declName_1451_);
lean_del_object(v___x_1317_);
lean_dec_ref(v_k_1295_);
lean_dec_ref(v_decl_1294_);
v___x_1474_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4);
v___x_1475_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1474_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1475_;
}
else
{
lean_object* v_val_1476_; 
v_val_1476_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_val_1476_);
lean_dec_ref(v___x_1473_);
switch(lean_obj_tag(v_val_1476_))
{
case 0:
{
lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_a_1456_);
lean_dec_ref(v_args_1452_);
lean_dec_ref(v_k_1295_);
lean_dec_ref(v_decl_1294_);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_val_1476_);
if (v_isSharedCheck_1492_ == 0)
{
lean_object* v_unused_1493_; 
v_unused_1493_ = lean_ctor_get(v_val_1476_, 0);
lean_dec(v_unused_1493_);
v___x_1478_ = v_val_1476_;
v_isShared_1479_ = v_isSharedCheck_1492_;
goto v_resetjp_1477_;
}
else
{
lean_dec(v_val_1476_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1492_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1483_; 
v___x_1480_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1481_ = l_Lean_Name_toString(v_declName_1451_, v___x_1320_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set_tag(v___x_1478_, 3);
lean_ctor_set(v___x_1478_, 0, v___x_1481_);
v___x_1483_ = v___x_1478_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1485_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set_tag(v___x_1317_, 5);
lean_ctor_set(v___x_1317_, 1, v___x_1483_);
lean_ctor_set(v___x_1317_, 0, v___x_1480_);
v___x_1485_ = v___x_1317_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1486_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1487_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1485_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = l_Lean_MessageData_ofFormat(v___x_1487_);
v___x_1489_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1488_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1489_;
}
}
}
}
case 2:
{
lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1509_; 
lean_dec(v_a_1456_);
lean_dec_ref(v_args_1452_);
lean_dec_ref(v_k_1295_);
lean_dec_ref(v_decl_1294_);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_val_1476_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; 
v_unused_1510_ = lean_ctor_get(v_val_1476_, 0);
lean_dec(v_unused_1510_);
v___x_1495_ = v_val_1476_;
v_isShared_1496_ = v_isSharedCheck_1509_;
goto v_resetjp_1494_;
}
else
{
lean_dec(v_val_1476_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1509_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1497_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1498_ = l_Lean_Name_toString(v_declName_1451_, v___x_1320_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set_tag(v___x_1495_, 3);
lean_ctor_set(v___x_1495_, 0, v___x_1498_);
v___x_1500_ = v___x_1495_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1502_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set_tag(v___x_1317_, 5);
lean_ctor_set(v___x_1317_, 1, v___x_1500_);
lean_ctor_set(v___x_1317_, 0, v___x_1497_);
v___x_1502_ = v___x_1317_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1503_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1504_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1502_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
v___x_1505_ = l_Lean_MessageData_ofFormat(v___x_1504_);
v___x_1506_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1505_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1506_;
}
}
}
}
case 4:
{
lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1526_; 
lean_dec(v_a_1456_);
lean_dec_ref(v_args_1452_);
lean_dec_ref(v_k_1295_);
lean_dec_ref(v_decl_1294_);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_val_1476_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; 
v_unused_1527_ = lean_ctor_get(v_val_1476_, 0);
lean_dec(v_unused_1527_);
v___x_1512_ = v_val_1476_;
v_isShared_1513_ = v_isSharedCheck_1526_;
goto v_resetjp_1511_;
}
else
{
lean_dec(v_val_1476_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1526_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1517_; 
v___x_1514_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1515_ = l_Lean_Name_toString(v_declName_1451_, v___x_1320_);
if (v_isShared_1513_ == 0)
{
lean_ctor_set_tag(v___x_1512_, 3);
lean_ctor_set(v___x_1512_, 0, v___x_1515_);
v___x_1517_ = v___x_1512_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1515_);
v___x_1517_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1519_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set_tag(v___x_1317_, 5);
lean_ctor_set(v___x_1317_, 1, v___x_1517_);
lean_ctor_set(v___x_1317_, 0, v___x_1514_);
v___x_1519_ = v___x_1317_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v___x_1517_);
v___x_1519_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1520_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1521_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1519_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___x_1522_ = l_Lean_MessageData_ofFormat(v___x_1521_);
v___x_1523_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1522_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1523_;
}
}
}
}
case 5:
{
lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1543_; 
lean_dec(v_a_1456_);
lean_dec_ref(v_args_1452_);
lean_dec_ref(v_k_1295_);
lean_dec_ref(v_decl_1294_);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_val_1476_);
if (v_isSharedCheck_1543_ == 0)
{
lean_object* v_unused_1544_; 
v_unused_1544_ = lean_ctor_get(v_val_1476_, 0);
lean_dec(v_unused_1544_);
v___x_1529_ = v_val_1476_;
v_isShared_1530_ = v_isSharedCheck_1543_;
goto v_resetjp_1528_;
}
else
{
lean_dec(v_val_1476_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1543_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1531_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1532_ = l_Lean_Name_toString(v_declName_1451_, v___x_1320_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set_tag(v___x_1529_, 3);
lean_ctor_set(v___x_1529_, 0, v___x_1532_);
v___x_1534_ = v___x_1529_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1536_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set_tag(v___x_1317_, 5);
lean_ctor_set(v___x_1317_, 1, v___x_1534_);
lean_ctor_set(v___x_1317_, 0, v___x_1531_);
v___x_1536_ = v___x_1317_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1537_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1538_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1536_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = l_Lean_MessageData_ofFormat(v___x_1538_);
v___x_1540_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1539_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1540_;
}
}
}
}
case 6:
{
lean_object* v_val_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1680_; 
v_val_1545_ = lean_ctor_get(v_val_1476_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_val_1476_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1547_ = v_val_1476_;
v_isShared_1548_ = v_isSharedCheck_1680_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_val_1545_);
lean_dec(v_val_1476_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1680_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v_induct_1549_; lean_object* v_cidx_1550_; lean_object* v_numParams_1551_; lean_object* v___x_1552_; 
v_induct_1549_ = lean_ctor_get(v_val_1545_, 1);
lean_inc_n(v_induct_1549_, 2);
v_cidx_1550_ = lean_ctor_get(v_val_1545_, 2);
lean_inc(v_cidx_1550_);
v_numParams_1551_ = lean_ctor_get(v_val_1545_, 3);
lean_inc(v_numParams_1551_);
lean_dec_ref(v_val_1545_);
v___x_1552_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_induct_1549_, v_a_1299_, v_a_1300_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref(v___x_1552_);
if (lean_obj_tag(v_a_1553_) == 1)
{
lean_object* v_val_1554_; lean_object* v___x_1555_; lean_object* v_numParams_1556_; lean_object* v_fieldIdx_1557_; lean_object* v_subst_1558_; lean_object* v_jpParamMask_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1572_; 
lean_inc(v_fvarId_1311_);
lean_dec(v_numParams_1551_);
lean_dec(v_cidx_1550_);
lean_dec(v_induct_1549_);
lean_del_object(v___x_1547_);
lean_dec(v_a_1456_);
lean_dec(v_declName_1451_);
lean_del_object(v___x_1317_);
lean_dec_ref(v_decl_1294_);
v_val_1554_ = lean_ctor_get(v_a_1553_, 0);
lean_inc(v_val_1554_);
lean_dec_ref(v_a_1553_);
v___x_1555_ = lean_st_ref_take(v_a_1296_);
v_numParams_1556_ = lean_ctor_get(v_val_1554_, 1);
lean_inc(v_numParams_1556_);
v_fieldIdx_1557_ = lean_ctor_get(v_val_1554_, 2);
lean_inc(v_fieldIdx_1557_);
lean_dec(v_val_1554_);
v_subst_1558_ = lean_ctor_get(v___x_1555_, 0);
v_jpParamMask_1559_ = lean_ctor_get(v___x_1555_, 1);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1561_ = v___x_1555_;
v_isShared_1562_ = v_isSharedCheck_1572_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_jpParamMask_1559_);
lean_inc(v_subst_1558_);
lean_dec(v___x_1555_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1572_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1568_; 
v___x_1563_ = lean_box(0);
v___x_1564_ = lean_nat_add(v_numParams_1556_, v_fieldIdx_1557_);
lean_dec(v_fieldIdx_1557_);
lean_dec(v_numParams_1556_);
v___x_1565_ = lean_array_get(v___x_1563_, v_args_1452_, v___x_1564_);
lean_dec(v___x_1564_);
lean_dec_ref(v_args_1452_);
v___x_1566_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1558_, v_fvarId_1311_, v___x_1565_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1566_);
v___x_1568_ = v___x_1561_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_jpParamMask_1559_);
v___x_1568_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = lean_st_ref_set(v_a_1296_, v___x_1568_);
v___x_1570_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1570_;
}
}
}
else
{
lean_object* v___x_1573_; 
lean_dec(v_a_1553_);
lean_dec_ref(v_args_1452_);
v___x_1573_ = l_Lean_Compiler_LCNF_nameToImpureType(v_induct_1549_, v_a_1299_, v_a_1300_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; uint8_t v___x_1575_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
lean_dec_ref(v___x_1573_);
v___x_1575_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_1574_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; 
lean_dec(v_a_1574_);
lean_dec(v_cidx_1550_);
lean_del_object(v___x_1547_);
v___x_1576_ = l_Lean_Compiler_LCNF_getCtorLayout(v_declName_1451_, v_a_1299_, v_a_1300_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1639_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1579_ = v___x_1576_;
v_isShared_1580_ = v_isSharedCheck_1639_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1639_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v_ctorInfo_1586_; lean_object* v_fieldInfo_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1638_; 
v_ctorInfo_1586_ = lean_ctor_get(v_a_1577_, 0);
v_fieldInfo_1587_ = lean_ctor_get(v_a_1577_, 1);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_a_1577_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1589_ = v_a_1577_;
v_isShared_1590_ = v_isSharedCheck_1638_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_fieldInfo_1587_);
lean_inc(v_ctorInfo_1586_);
lean_dec(v_a_1577_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1638_;
goto v_resetjp_1588_;
}
v___jp_1581_:
{
lean_object* v___x_1582_; lean_object* v___x_1584_; 
v___x_1582_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v___x_1582_);
v___x_1584_ = v___x_1579_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
v_resetjp_1588_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v___x_1591_ = lean_array_get_size(v_a_1456_);
v___x_1592_ = l_Array_extract___redArg(v_a_1456_, v_numParams_1551_, v___x_1591_);
lean_dec(v_a_1456_);
v___x_1593_ = lean_array_get_size(v___x_1592_);
v___x_1594_ = lean_array_get_size(v_fieldInfo_1587_);
v___x_1595_ = lean_nat_dec_eq(v___x_1593_, v___x_1594_);
if (v___x_1595_ == 0)
{
lean_dec_ref(v___x_1592_);
lean_del_object(v___x_1589_);
lean_dec_ref(v_fieldInfo_1587_);
lean_dec_ref(v_ctorInfo_1586_);
lean_del_object(v___x_1317_);
lean_dec_ref(v_k_1295_);
lean_dec_ref(v_decl_1294_);
goto v___jp_1581_;
}
else
{
if (v___x_1575_ == 0)
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_del_object(v___x_1579_);
v___x_1596_ = lean_unsigned_to_nat(0u);
v___x_1597_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4));
v___x_1598_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_1594_, v_fieldInfo_1587_, v___x_1592_, v___x_1596_, v___x_1597_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1600_; lean_object* v_lctx_1601_; lean_object* v_nextIdx_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1629_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref(v___x_1598_);
v___x_1600_ = lean_st_ref_take(v_a_1298_);
v_lctx_1601_ = lean_ctor_get(v___x_1600_, 0);
v_nextIdx_1602_ = lean_ctor_get(v___x_1600_, 1);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1604_ = v___x_1600_;
v_isShared_1605_ = v_isSharedCheck_1629_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_nextIdx_1602_);
lean_inc(v_lctx_1601_);
lean_dec(v___x_1600_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1629_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; uint8_t v___x_1607_; lean_object* v___x_1609_; 
v___x_1606_ = l_Lean_Compiler_LCNF_CtorInfo_type(v_ctorInfo_1586_);
v___x_1607_ = 1;
lean_inc_ref(v_ctorInfo_1586_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set_tag(v___x_1589_, 5);
lean_ctor_set(v___x_1589_, 1, v_a_1599_);
v___x_1609_ = v___x_1589_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_ctorInfo_1586_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_a_1599_);
v___x_1609_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1613_; 
lean_inc(v_binderName_1312_);
lean_inc(v_fvarId_1311_);
v___x_1610_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1610_, 0, v_fvarId_1311_);
lean_ctor_set(v___x_1610_, 1, v_binderName_1312_);
lean_ctor_set(v___x_1610_, 2, v___x_1606_);
lean_ctor_set(v___x_1610_, 3, v___x_1609_);
lean_inc_ref(v___x_1610_);
v___x_1611_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1607_, v_lctx_1601_, v___x_1610_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1611_);
v___x_1613_ = v___x_1604_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_nextIdx_1602_);
v___x_1613_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_st_ref_set(v_a_1298_, v___x_1613_);
v___x_1615_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(v_decl_1294_, v_k_1295_, v_ctorInfo_1586_, v_fieldInfo_1587_, v___x_1592_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
lean_dec_ref(v___x_1592_);
lean_dec_ref(v_fieldInfo_1587_);
lean_dec_ref(v_ctorInfo_1586_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1626_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1626_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1626_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 1, v_a_1616_);
lean_ctor_set(v___x_1317_, 0, v___x_1610_);
v___x_1621_ = v___x_1317_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1610_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1623_; 
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v___x_1621_);
v___x_1623_ = v___x_1618_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
else
{
lean_dec_ref(v___x_1610_);
lean_del_object(v___x_1317_);
return v___x_1615_;
}
}
}
}
}
else
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec_ref(v___x_1592_);
lean_del_object(v___x_1589_);
lean_dec_ref(v_fieldInfo_1587_);
lean_dec_ref(v_ctorInfo_1586_);
lean_del_object(v___x_1317_);
lean_dec_ref(v_k_1295_);
lean_dec_ref(v_decl_1294_);
v_a_1630_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1598_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1598_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
else
{
lean_dec_ref(v___x_1592_);
lean_del_object(v___x_1589_);
lean_dec_ref(v_fieldInfo_1587_);
lean_dec_ref(v_ctorInfo_1586_);
lean_del_object(v___x_1317_);
lean_dec_ref(v_k_1295_);
lean_dec_ref(v_decl_1294_);
goto v___jp_1581_;
}
}
}
}
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec(v_numParams_1551_);
lean_dec(v_a_1456_);
lean_del_object(v___x_1317_);
lean_dec_ref(v_k_1295_);
lean_dec_ref(v_decl_1294_);
v_a_1640_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1576_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1576_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
else
{
lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1659_; 
lean_inc(v_binderName_1312_);
lean_inc(v_fvarId_1311_);
lean_dec(v_numParams_1551_);
lean_dec(v_a_1456_);
lean_dec(v_declName_1451_);
lean_del_object(v___x_1317_);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_decl_1294_);
if (v_isSharedCheck_1659_ == 0)
{
lean_object* v_unused_1660_; lean_object* v_unused_1661_; lean_object* v_unused_1662_; lean_object* v_unused_1663_; 
v_unused_1660_ = lean_ctor_get(v_decl_1294_, 3);
lean_dec(v_unused_1660_);
v_unused_1661_ = lean_ctor_get(v_decl_1294_, 2);
lean_dec(v_unused_1661_);
v_unused_1662_ = lean_ctor_get(v_decl_1294_, 1);
lean_dec(v_unused_1662_);
v_unused_1663_ = lean_ctor_get(v_decl_1294_, 0);
lean_dec(v_unused_1663_);
v___x_1649_ = v_decl_1294_;
v_isShared_1650_ = v_isSharedCheck_1659_;
goto v_resetjp_1648_;
}
else
{
lean_dec(v_decl_1294_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1659_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1651_ = l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(v_a_1574_, v_cidx_1550_);
lean_dec(v_cidx_1550_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set_tag(v___x_1547_, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1651_);
v___x_1653_ = v___x_1547_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1655_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 3, v___x_1653_);
lean_ctor_set(v___x_1649_, 2, v_a_1574_);
v___x_1655_ = v___x_1649_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_fvarId_1311_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_binderName_1312_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v_a_1574_);
lean_ctor_set(v_reuseFailAlloc_1657_, 3, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1656_; 
v___x_1656_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1295_, v___x_1655_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1656_;
}
}
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_dec(v_numParams_1551_);
lean_dec(v_cidx_1550_);
lean_del_object(v___x_1547_);
lean_dec(v_a_1456_);
lean_dec(v_declName_1451_);
lean_del_object(v___x_1317_);
lean_dec_ref(v_k_1295_);
lean_dec_ref(v_decl_1294_);
v_a_1664_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1573_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1573_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec(v_numParams_1551_);
lean_dec(v_cidx_1550_);
lean_dec(v_induct_1549_);
lean_del_object(v___x_1547_);
lean_dec(v_a_1456_);
lean_dec_ref(v_args_1452_);
lean_dec(v_declName_1451_);
lean_del_object(v___x_1317_);
lean_dec_ref(v_k_1295_);
lean_dec_ref(v_decl_1294_);
v_a_1672_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1552_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1552_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
}
case 7:
{
lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1696_; 
lean_dec(v_a_1456_);
lean_dec_ref(v_args_1452_);
lean_dec_ref(v_k_1295_);
lean_dec_ref(v_decl_1294_);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_val_1476_);
if (v_isSharedCheck_1696_ == 0)
{
lean_object* v_unused_1697_; 
v_unused_1697_ = lean_ctor_get(v_val_1476_, 0);
lean_dec(v_unused_1697_);
v___x_1682_ = v_val_1476_;
v_isShared_1683_ = v_isSharedCheck_1696_;
goto v_resetjp_1681_;
}
else
{
lean_dec(v_val_1476_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1696_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1687_; 
v___x_1684_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11));
v___x_1685_ = l_Lean_Name_toString(v_declName_1451_, v___x_1320_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set_tag(v___x_1682_, 3);
lean_ctor_set(v___x_1682_, 0, v___x_1685_);
v___x_1687_ = v___x_1682_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1689_; 
if (v_isShared_1318_ == 0)
{
lean_ctor_set_tag(v___x_1317_, 5);
lean_ctor_set(v___x_1317_, 1, v___x_1687_);
lean_ctor_set(v___x_1317_, 0, v___x_1684_);
v___x_1689_ = v___x_1317_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1690_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13));
v___x_1691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1689_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = l_Lean_MessageData_ofFormat(v___x_1691_);
v___x_1693_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1692_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1693_;
}
}
}
}
default: 
{
lean_object* v___x_1698_; 
lean_dec(v_val_1476_);
lean_dec_ref(v_args_1452_);
lean_del_object(v___x_1317_);
v___x_1698_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_1294_, v_k_1295_, v_declName_1451_, v_a_1456_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1698_;
}
}
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec(v_a_1456_);
lean_dec_ref(v_args_1452_);
lean_dec(v_declName_1451_);
lean_del_object(v___x_1317_);
lean_dec_ref(v_k_1295_);
lean_dec_ref(v_decl_1294_);
v_a_1699_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1463_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1463_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec(v_a_1456_);
lean_dec_ref(v_args_1452_);
lean_dec(v_declName_1451_);
lean_del_object(v___x_1317_);
lean_dec_ref(v_k_1295_);
lean_dec_ref(v_decl_1294_);
v_a_1707_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1457_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1457_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec_ref(v_args_1452_);
lean_dec(v_declName_1451_);
lean_del_object(v___x_1317_);
lean_dec_ref(v_k_1295_);
lean_dec_ref(v_decl_1294_);
v_a_1715_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1455_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1455_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
default: 
{
lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1762_; 
lean_inc_ref(v_type_1313_);
lean_inc(v_binderName_1312_);
lean_inc(v_fvarId_1311_);
lean_del_object(v___x_1317_);
v_isSharedCheck_1762_ = !lean_is_exclusive(v_decl_1294_);
if (v_isSharedCheck_1762_ == 0)
{
lean_object* v_unused_1763_; lean_object* v_unused_1764_; lean_object* v_unused_1765_; lean_object* v_unused_1766_; 
v_unused_1763_ = lean_ctor_get(v_decl_1294_, 3);
lean_dec(v_unused_1763_);
v_unused_1764_ = lean_ctor_get(v_decl_1294_, 2);
lean_dec(v_unused_1764_);
v_unused_1765_ = lean_ctor_get(v_decl_1294_, 1);
lean_dec(v_unused_1765_);
v_unused_1766_ = lean_ctor_get(v_decl_1294_, 0);
lean_dec(v_unused_1766_);
v___x_1724_ = v_decl_1294_;
v_isShared_1725_ = v_isSharedCheck_1762_;
goto v_resetjp_1723_;
}
else
{
lean_dec(v_decl_1294_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1762_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v_fvarId_1726_; lean_object* v_args_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1761_; 
v_fvarId_1726_ = lean_ctor_get(v___x_1321_, 0);
v_args_1727_ = lean_ctor_get(v___x_1321_, 1);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1729_ = v___x_1321_;
v_isShared_1730_ = v_isSharedCheck_1761_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_args_1727_);
lean_inc(v_fvarId_1726_);
lean_dec(v___x_1321_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1761_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
size_t v_sz_1731_; size_t v___x_1732_; lean_object* v___x_1733_; 
v_sz_1731_ = lean_array_size(v_args_1727_);
v___x_1732_ = ((size_t)0ULL);
v___x_1733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_1731_, v___x_1732_, v_args_1727_, v_a_1296_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; lean_object* v___x_1735_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_a_1734_);
lean_dec_ref(v___x_1733_);
v___x_1735_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1313_, v_a_1299_, v_a_1300_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1737_; lean_object* v___x_1739_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref(v___x_1735_);
v___x_1737_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_a_1736_);
lean_dec(v_a_1736_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 1, v_a_1734_);
v___x_1739_ = v___x_1729_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_fvarId_1726_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_a_1734_);
v___x_1739_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
lean_object* v___x_1741_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 3, v___x_1739_);
lean_ctor_set(v___x_1724_, 2, v___x_1737_);
v___x_1741_ = v___x_1724_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_fvarId_1311_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_binderName_1312_);
lean_ctor_set(v_reuseFailAlloc_1743_, 2, v___x_1737_);
lean_ctor_set(v_reuseFailAlloc_1743_, 3, v___x_1739_);
v___x_1741_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; 
v___x_1742_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1295_, v___x_1741_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1742_;
}
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_dec(v_a_1734_);
lean_del_object(v___x_1729_);
lean_dec(v_fvarId_1726_);
lean_del_object(v___x_1724_);
lean_dec(v_binderName_1312_);
lean_dec(v_fvarId_1311_);
lean_dec_ref(v_k_1295_);
v_a_1745_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1735_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1735_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_del_object(v___x_1729_);
lean_dec(v_fvarId_1726_);
lean_del_object(v___x_1724_);
lean_dec_ref(v_type_1313_);
lean_dec(v_binderName_1312_);
lean_dec(v_fvarId_1311_);
lean_dec_ref(v_k_1295_);
v_a_1753_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1733_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1733_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1771_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1));
v___x_1772_ = lean_unsigned_to_nat(15u);
v___x_1773_ = lean_unsigned_to_nat(272u);
v___x_1774_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1775_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1776_ = l_mkPanicMessageWithDecl(v___x_1775_, v___x_1774_, v___x_1773_, v___x_1772_, v___x_1771_);
return v___x_1776_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1780_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5));
v___x_1781_ = lean_unsigned_to_nat(6u);
v___x_1782_ = lean_unsigned_to_nat(251u);
v___x_1783_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1784_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1785_ = l_mkPanicMessageWithDecl(v___x_1784_, v___x_1783_, v___x_1782_, v___x_1781_, v___x_1780_);
return v___x_1785_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7(void){
_start:
{
uint8_t v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = 0;
v___x_1787_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v___x_1786_);
return v___x_1787_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1789_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8));
v___x_1790_ = lean_unsigned_to_nat(6u);
v___x_1791_ = lean_unsigned_to_nat(253u);
v___x_1792_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1793_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1794_ = l_mkPanicMessageWithDecl(v___x_1793_, v___x_1792_, v___x_1791_, v___x_1790_, v___x_1789_);
return v___x_1794_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1796_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10));
v___x_1797_ = lean_unsigned_to_nat(6u);
v___x_1798_ = lean_unsigned_to_nat(254u);
v___x_1799_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1800_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1801_ = l_mkPanicMessageWithDecl(v___x_1800_, v___x_1799_, v___x_1798_, v___x_1797_, v___x_1796_);
return v___x_1801_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1803_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12));
v___x_1804_ = lean_unsigned_to_nat(45u);
v___x_1805_ = lean_unsigned_to_nat(252u);
v___x_1806_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1807_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1808_ = l_mkPanicMessageWithDecl(v___x_1807_, v___x_1806_, v___x_1805_, v___x_1804_, v___x_1803_);
return v___x_1808_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1811_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1));
v___x_1812_ = lean_unsigned_to_nat(18u);
v___x_1813_ = lean_unsigned_to_nat(293u);
v___x_1814_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0));
v___x_1815_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1816_ = l_mkPanicMessageWithDecl(v___x_1815_, v___x_1814_, v___x_1813_, v___x_1812_, v___x_1811_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(lean_object* v_discr_1817_, lean_object* v_k_1818_, lean_object* v_ctorInfo_1819_, lean_object* v_params_1820_, lean_object* v_fields_1821_, lean_object* v_i_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1899_; lean_object* v___x_1905_; uint8_t v___x_1906_; 
v___x_1905_ = lean_array_get_size(v_params_1820_);
v___x_1906_ = lean_nat_dec_lt(v_i_1822_, v___x_1905_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; 
v___x_1907_ = lean_box(0);
v___y_1899_ = v___x_1907_;
goto v___jp_1898_;
}
else
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = lean_array_fget_borrowed(v_params_1820_, v_i_1822_);
lean_inc(v___x_1908_);
v___x_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
v___y_1899_ = v___x_1909_;
goto v___jp_1898_;
}
v___jp_1829_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2);
v___x_1836_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1835_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_);
return v___x_1836_;
}
v___jp_1837_:
{
if (lean_obj_tag(v___y_1838_) == 0)
{
lean_dec(v_i_1822_);
lean_dec(v_discr_1817_);
if (lean_obj_tag(v___y_1839_) == 0)
{
lean_object* v___x_1840_; 
v___x_1840_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1818_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_);
return v___x_1840_;
}
else
{
lean_dec(v___y_1839_);
lean_dec_ref(v_k_1818_);
v___y_1830_ = v_a_1823_;
v___y_1831_ = v_a_1824_;
v___y_1832_ = v_a_1825_;
v___y_1833_ = v_a_1826_;
v___y_1834_ = v_a_1827_;
goto v___jp_1829_;
}
}
else
{
if (lean_obj_tag(v___y_1839_) == 1)
{
lean_object* v_val_1841_; lean_object* v_val_1842_; lean_object* v___x_1843_; lean_object* v_fst_1844_; 
v_val_1841_ = lean_ctor_get(v___y_1838_, 0);
lean_inc(v_val_1841_);
lean_dec_ref(v___y_1838_);
v_val_1842_ = lean_ctor_get(v___y_1839_, 0);
lean_inc(v_val_1842_);
lean_dec_ref(v___y_1839_);
lean_inc(v_discr_1817_);
v___x_1843_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_discr_1817_, v_ctorInfo_1819_, v_val_1842_);
v_fst_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_fst_1844_);
if (lean_obj_tag(v_fst_1844_) == 1)
{
lean_object* v___x_1845_; lean_object* v_fvarId_1846_; lean_object* v_subst_1847_; lean_object* v_jpParamMask_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1861_; 
lean_dec_ref(v___x_1843_);
v___x_1845_ = lean_st_ref_take(v_a_1823_);
v_fvarId_1846_ = lean_ctor_get(v_val_1841_, 0);
lean_inc(v_fvarId_1846_);
lean_dec(v_val_1841_);
v_subst_1847_ = lean_ctor_get(v___x_1845_, 0);
v_jpParamMask_1848_ = lean_ctor_get(v___x_1845_, 1);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1850_ = v___x_1845_;
v_isShared_1851_ = v_isSharedCheck_1861_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_jpParamMask_1848_);
lean_inc(v_subst_1847_);
lean_dec(v___x_1845_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1861_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1852_ = lean_box(0);
v___x_1853_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1847_, v_fvarId_1846_, v___x_1852_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1853_);
v___x_1855_ = v___x_1850_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1853_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_jpParamMask_1848_);
v___x_1855_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1856_ = lean_st_ref_set(v_a_1823_, v___x_1855_);
v___x_1857_ = lean_unsigned_to_nat(1u);
v___x_1858_ = lean_nat_add(v_i_1822_, v___x_1857_);
lean_dec(v_i_1822_);
v_i_1822_ = v___x_1858_;
goto _start;
}
}
}
else
{
lean_object* v_snd_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1896_; 
v_snd_1862_ = lean_ctor_get(v___x_1843_, 1);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1896_ == 0)
{
lean_object* v_unused_1897_; 
v_unused_1897_ = lean_ctor_get(v___x_1843_, 0);
lean_dec(v_unused_1897_);
v___x_1864_ = v___x_1843_;
v_isShared_1865_ = v_isSharedCheck_1896_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_snd_1862_);
lean_dec(v___x_1843_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1896_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1866_; lean_object* v_fvarId_1867_; lean_object* v_binderName_1868_; lean_object* v_lctx_1869_; lean_object* v_nextIdx_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1895_; 
v___x_1866_ = lean_st_ref_take(v_a_1825_);
v_fvarId_1867_ = lean_ctor_get(v_val_1841_, 0);
lean_inc(v_fvarId_1867_);
v_binderName_1868_ = lean_ctor_get(v_val_1841_, 1);
lean_inc(v_binderName_1868_);
lean_dec(v_val_1841_);
v_lctx_1869_ = lean_ctor_get(v___x_1866_, 0);
v_nextIdx_1870_ = lean_ctor_get(v___x_1866_, 1);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1872_ = v___x_1866_;
v_isShared_1873_ = v_isSharedCheck_1895_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_nextIdx_1870_);
lean_inc(v_lctx_1869_);
lean_dec(v___x_1866_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1895_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
uint8_t v___x_1874_; lean_object* v_decl_1875_; lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1874_ = 1;
v_decl_1875_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_decl_1875_, 0, v_fvarId_1867_);
lean_ctor_set(v_decl_1875_, 1, v_binderName_1868_);
lean_ctor_set(v_decl_1875_, 2, v_snd_1862_);
lean_ctor_set(v_decl_1875_, 3, v_fst_1844_);
lean_inc_ref(v_decl_1875_);
v___x_1876_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1874_, v_lctx_1869_, v_decl_1875_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1876_);
v___x_1878_ = v___x_1872_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1876_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_nextIdx_1870_);
v___x_1878_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1879_ = lean_st_ref_set(v_a_1825_, v___x_1878_);
v___x_1880_ = lean_unsigned_to_nat(1u);
v___x_1881_ = lean_nat_add(v_i_1822_, v___x_1880_);
lean_dec(v_i_1822_);
v___x_1882_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_1817_, v_k_1818_, v_ctorInfo_1819_, v_params_1820_, v_fields_1821_, v___x_1881_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1893_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1885_ = v___x_1882_;
v_isShared_1886_ = v_isSharedCheck_1893_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1893_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 1, v_a_1883_);
lean_ctor_set(v___x_1864_, 0, v_decl_1875_);
v___x_1888_ = v___x_1864_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_decl_1875_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1890_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1888_);
v___x_1890_ = v___x_1885_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
else
{
lean_dec_ref(v_decl_1875_);
lean_del_object(v___x_1864_);
return v___x_1882_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1839_);
lean_dec(v_i_1822_);
lean_dec_ref(v_k_1818_);
lean_dec(v_discr_1817_);
v___y_1830_ = v_a_1823_;
v___y_1831_ = v_a_1824_;
v___y_1832_ = v_a_1825_;
v___y_1833_ = v_a_1826_;
v___y_1834_ = v_a_1827_;
goto v___jp_1829_;
}
}
}
v___jp_1898_:
{
lean_object* v___x_1900_; uint8_t v___x_1901_; 
v___x_1900_ = lean_array_get_size(v_fields_1821_);
v___x_1901_ = lean_nat_dec_lt(v_i_1822_, v___x_1900_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; 
v___x_1902_ = lean_box(0);
v___y_1838_ = v___y_1899_;
v___y_1839_ = v___x_1902_;
goto v___jp_1837_;
}
else
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = lean_array_fget_borrowed(v_fields_1821_, v_i_1822_);
lean_inc(v___x_1903_);
v___x_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
v___y_1838_ = v___y_1899_;
v___y_1839_ = v___x_1904_;
goto v___jp_1837_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(lean_object* v_discr_1910_, lean_object* v_alt_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_){
_start:
{
if (lean_obj_tag(v_alt_1911_) == 0)
{
lean_object* v_ctorName_1918_; lean_object* v_params_1919_; lean_object* v_code_1920_; lean_object* v___x_1921_; 
v_ctorName_1918_ = lean_ctor_get(v_alt_1911_, 0);
lean_inc(v_ctorName_1918_);
v_params_1919_ = lean_ctor_get(v_alt_1911_, 1);
lean_inc_ref(v_params_1919_);
v_code_1920_ = lean_ctor_get(v_alt_1911_, 2);
lean_inc_ref(v_code_1920_);
lean_dec_ref(v_alt_1911_);
v___x_1921_ = l_Lean_Compiler_LCNF_getCtorLayout(v_ctorName_1918_, v_a_1915_, v_a_1916_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; lean_object* v_ctorInfo_1923_; lean_object* v_fieldInfo_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1949_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref(v___x_1921_);
v_ctorInfo_1923_ = lean_ctor_get(v_a_1922_, 0);
v_fieldInfo_1924_ = lean_ctor_get(v_a_1922_, 1);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_a_1922_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1926_ = v_a_1922_;
v_isShared_1927_ = v_isSharedCheck_1949_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_fieldInfo_1924_);
lean_inc(v_ctorInfo_1923_);
lean_dec(v_a_1922_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1949_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_unsigned_to_nat(0u);
v___x_1929_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_1910_, v_code_1920_, v_ctorInfo_1923_, v_params_1919_, v_fieldInfo_1924_, v___x_1928_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_);
lean_dec_ref(v_fieldInfo_1924_);
lean_dec_ref(v_params_1919_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1940_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1932_ = v___x_1929_;
v_isShared_1933_ = v_isSharedCheck_1940_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1929_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1940_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1927_ == 0)
{
lean_ctor_set_tag(v___x_1926_, 1);
lean_ctor_set(v___x_1926_, 1, v_a_1930_);
v___x_1935_ = v___x_1926_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_ctorInfo_1923_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1937_; 
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1935_);
v___x_1937_ = v___x_1932_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_del_object(v___x_1926_);
lean_dec_ref(v_ctorInfo_1923_);
v_a_1941_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1929_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1929_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec_ref(v_code_1920_);
lean_dec_ref(v_params_1919_);
lean_dec(v_discr_1910_);
v_a_1950_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1921_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1921_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
else
{
lean_object* v_code_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1982_; 
lean_dec(v_discr_1910_);
v_code_1958_ = lean_ctor_get(v_alt_1911_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_alt_1911_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1960_ = v_alt_1911_;
v_isShared_1961_ = v_isSharedCheck_1982_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_code_1958_);
lean_dec(v_alt_1911_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1982_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1962_; 
v___x_1962_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_code_1958_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1973_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1965_ = v___x_1962_;
v_isShared_1966_ = v_isSharedCheck_1973_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1962_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1973_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v_a_1963_);
v___x_1968_ = v___x_1960_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1970_; 
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v___x_1968_);
v___x_1970_ = v___x_1965_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
else
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1981_; 
lean_del_object(v___x_1960_);
v_a_1974_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1976_ = v___x_1962_;
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1962_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1981_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_a_1974_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(lean_object* v_fvarId_1983_, size_t v_sz_1984_, size_t v_i_1985_, lean_object* v_bs_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
uint8_t v___x_1993_; 
v___x_1993_ = lean_usize_dec_lt(v_i_1985_, v_sz_1984_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1994_; 
lean_dec(v_fvarId_1983_);
v___x_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1994_, 0, v_bs_1986_);
return v___x_1994_;
}
else
{
lean_object* v_v_1995_; lean_object* v___x_1996_; 
v_v_1995_ = lean_array_uget_borrowed(v_bs_1986_, v_i_1985_);
lean_inc(v_v_1995_);
lean_inc(v_fvarId_1983_);
v___x_1996_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(v_fvarId_1983_, v_v_1995_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1998_; lean_object* v_bs_x27_1999_; size_t v___x_2000_; size_t v___x_2001_; lean_object* v___x_2002_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref(v___x_1996_);
v___x_1998_ = lean_unsigned_to_nat(0u);
v_bs_x27_1999_ = lean_array_uset(v_bs_1986_, v_i_1985_, v___x_1998_);
v___x_2000_ = ((size_t)1ULL);
v___x_2001_ = lean_usize_add(v_i_1985_, v___x_2000_);
v___x_2002_ = lean_array_uset(v_bs_x27_1999_, v_i_1985_, v_a_1997_);
v_i_1985_ = v___x_2001_;
v_bs_1986_ = v___x_2002_;
goto _start;
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
lean_dec_ref(v_bs_1986_);
lean_dec(v_fvarId_1983_);
v_a_2004_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_1996_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_1996_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(lean_object* v_c_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_){
_start:
{
switch(lean_obj_tag(v_c_2012_))
{
case 0:
{
lean_object* v_decl_2019_; lean_object* v_k_2020_; lean_object* v___x_2021_; 
v_decl_2019_ = lean_ctor_get(v_c_2012_, 0);
lean_inc_ref(v_decl_2019_);
v_k_2020_ = lean_ctor_get(v_c_2012_, 1);
lean_inc_ref(v_k_2020_);
lean_dec_ref(v_c_2012_);
v___x_2021_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(v_decl_2019_, v_k_2020_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
return v___x_2021_;
}
case 1:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_dec_ref(v_c_2012_);
v___x_2022_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2);
v___x_2023_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2022_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
return v___x_2023_;
}
case 2:
{
lean_object* v_decl_2024_; lean_object* v_k_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2117_; 
v_decl_2024_ = lean_ctor_get(v_c_2012_, 0);
v_k_2025_ = lean_ctor_get(v_c_2012_, 1);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_c_2012_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2027_ = v_c_2012_;
v_isShared_2028_ = v_isSharedCheck_2117_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_k_2025_);
lean_inc(v_decl_2024_);
lean_dec(v_c_2012_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2117_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v_fvarId_2029_; lean_object* v_binderName_2030_; lean_object* v_params_2031_; lean_object* v_type_2032_; lean_object* v_value_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2116_; 
v_fvarId_2029_ = lean_ctor_get(v_decl_2024_, 0);
v_binderName_2030_ = lean_ctor_get(v_decl_2024_, 1);
v_params_2031_ = lean_ctor_get(v_decl_2024_, 2);
v_type_2032_ = lean_ctor_get(v_decl_2024_, 3);
v_value_2033_ = lean_ctor_get(v_decl_2024_, 4);
v_isSharedCheck_2116_ = !lean_is_exclusive(v_decl_2024_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2035_ = v_decl_2024_;
v_isShared_2036_ = v_isSharedCheck_2116_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_value_2033_);
lean_inc(v_type_2032_);
lean_inc(v_params_2031_);
lean_inc(v_binderName_2030_);
lean_inc(v_fvarId_2029_);
lean_dec(v_decl_2024_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2116_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
size_t v_sz_2037_; size_t v___x_2038_; lean_object* v___x_2039_; 
v_sz_2037_ = lean_array_size(v_params_2031_);
v___x_2038_ = ((size_t)0ULL);
v___x_2039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2037_, v___x_2038_, v_params_2031_, v_a_2013_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2041_; lean_object* v_subst_2042_; lean_object* v_jpParamMask_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2107_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref(v___x_2039_);
v___x_2041_ = lean_st_ref_take(v_a_2013_);
v_subst_2042_ = lean_ctor_get(v___x_2041_, 0);
v_jpParamMask_2043_ = lean_ctor_get(v___x_2041_, 1);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2045_ = v___x_2041_;
v_isShared_2046_ = v_isSharedCheck_2107_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_jpParamMask_2043_);
lean_inc(v_subst_2042_);
lean_dec(v___x_2041_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2107_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
size_t v_sz_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2051_; 
v_sz_2047_ = lean_array_size(v_a_2040_);
lean_inc(v_a_2040_);
v___x_2048_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(v_sz_2047_, v___x_2038_, v_a_2040_);
lean_inc_ref(v___x_2048_);
lean_inc(v_fvarId_2029_);
v___x_2049_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_jpParamMask_2043_, v_fvarId_2029_, v___x_2048_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 1, v___x_2049_);
v___x_2051_ = v___x_2045_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_subst_2042_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_object* v___x_2052_; lean_object* v___y_2054_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; 
v___x_2052_ = lean_st_ref_set(v_a_2013_, v___x_2051_);
v___x_2096_ = lean_unsigned_to_nat(0u);
v___x_2097_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3));
v___x_2098_ = l_Array_zip___redArg(v_a_2040_, v___x_2048_);
lean_dec_ref(v___x_2048_);
v___x_2099_ = lean_array_get_size(v___x_2098_);
v___x_2100_ = lean_nat_dec_lt(v___x_2096_, v___x_2099_);
if (v___x_2100_ == 0)
{
lean_dec_ref(v___x_2098_);
v___y_2054_ = v___x_2097_;
goto v___jp_2053_;
}
else
{
uint8_t v___x_2101_; 
v___x_2101_ = lean_nat_dec_le(v___x_2099_, v___x_2099_);
if (v___x_2101_ == 0)
{
if (v___x_2100_ == 0)
{
lean_dec_ref(v___x_2098_);
v___y_2054_ = v___x_2097_;
goto v___jp_2053_;
}
else
{
size_t v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = lean_usize_of_nat(v___x_2099_);
v___x_2103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v___x_2098_, v___x_2038_, v___x_2102_, v___x_2097_);
lean_dec_ref(v___x_2098_);
v___y_2054_ = v___x_2103_;
goto v___jp_2053_;
}
}
else
{
size_t v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = lean_usize_of_nat(v___x_2099_);
v___x_2105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v___x_2098_, v___x_2038_, v___x_2104_, v___x_2097_);
lean_dec_ref(v___x_2098_);
v___y_2054_ = v___x_2105_;
goto v___jp_2053_;
}
}
v___jp_2053_:
{
lean_object* v___x_2055_; 
v___x_2055_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_value_2033_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2057_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref(v___x_2055_);
v___x_2057_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_2025_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2058_);
lean_dec_ref(v___x_2057_);
v___x_2059_ = lean_array_get_size(v_a_2040_);
lean_dec(v_a_2040_);
v___x_2060_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_2032_, v___x_2059_, v_a_2016_, v_a_2017_);
lean_dec_ref(v_type_2032_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2087_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2063_ = v___x_2060_;
v_isShared_2064_ = v_isSharedCheck_2087_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2060_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2087_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2065_; lean_object* v_lctx_2066_; lean_object* v_nextIdx_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2086_; 
v___x_2065_ = lean_st_ref_take(v_a_2015_);
v_lctx_2066_ = lean_ctor_get(v___x_2065_, 0);
v_nextIdx_2067_ = lean_ctor_get(v___x_2065_, 1);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2069_ = v___x_2065_;
v_isShared_2070_ = v_isSharedCheck_2086_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_nextIdx_2067_);
lean_inc(v_lctx_2066_);
lean_dec(v___x_2065_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2086_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
uint8_t v___x_2071_; lean_object* v___x_2073_; 
v___x_2071_ = 1;
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 4, v_a_2056_);
lean_ctor_set(v___x_2035_, 3, v_a_2061_);
lean_ctor_set(v___x_2035_, 2, v___y_2054_);
v___x_2073_ = v___x_2035_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_fvarId_2029_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_binderName_2030_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v___y_2054_);
lean_ctor_set(v_reuseFailAlloc_2085_, 3, v_a_2061_);
lean_ctor_set(v_reuseFailAlloc_2085_, 4, v_a_2056_);
v___x_2073_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2074_; lean_object* v___x_2076_; 
lean_inc_ref(v___x_2073_);
v___x_2074_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v___x_2071_, v_lctx_2066_, v___x_2073_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2074_);
v___x_2076_ = v___x_2069_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2074_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_nextIdx_2067_);
v___x_2076_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
lean_object* v___x_2077_; lean_object* v___x_2079_; 
v___x_2077_ = lean_st_ref_set(v_a_2015_, v___x_2076_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 1, v_a_2058_);
lean_ctor_set(v___x_2027_, 0, v___x_2073_);
v___x_2079_ = v___x_2027_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2073_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_a_2058_);
v___x_2079_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2081_; 
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 0, v___x_2079_);
v___x_2081_ = v___x_2063_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec(v_a_2058_);
lean_dec(v_a_2056_);
lean_dec_ref(v___y_2054_);
lean_del_object(v___x_2035_);
lean_dec(v_binderName_2030_);
lean_dec(v_fvarId_2029_);
lean_del_object(v___x_2027_);
v_a_2088_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2060_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2060_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
else
{
lean_dec(v_a_2056_);
lean_dec_ref(v___y_2054_);
lean_dec(v_a_2040_);
lean_del_object(v___x_2035_);
lean_dec_ref(v_type_2032_);
lean_dec(v_binderName_2030_);
lean_dec(v_fvarId_2029_);
lean_del_object(v___x_2027_);
return v___x_2057_;
}
}
else
{
lean_dec_ref(v___y_2054_);
lean_dec(v_a_2040_);
lean_del_object(v___x_2035_);
lean_dec_ref(v_type_2032_);
lean_dec(v_binderName_2030_);
lean_dec(v_fvarId_2029_);
lean_del_object(v___x_2027_);
lean_dec_ref(v_k_2025_);
return v___x_2055_;
}
}
}
}
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_del_object(v___x_2035_);
lean_dec_ref(v_value_2033_);
lean_dec_ref(v_type_2032_);
lean_dec(v_binderName_2030_);
lean_dec(v_fvarId_2029_);
lean_del_object(v___x_2027_);
lean_dec_ref(v_k_2025_);
v_a_2108_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2039_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2039_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_2118_; lean_object* v_args_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2155_; 
v_fvarId_2118_ = lean_ctor_get(v_c_2012_, 0);
v_args_2119_ = lean_ctor_get(v_c_2012_, 1);
v_isSharedCheck_2155_ = !lean_is_exclusive(v_c_2012_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2121_ = v_c_2012_;
v_isShared_2122_ = v_isSharedCheck_2155_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_args_2119_);
lean_inc(v_fvarId_2118_);
lean_dec(v_c_2012_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2155_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v_a_2124_; lean_object* v___y_2130_; lean_object* v___x_2140_; lean_object* v_jpParamMask_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2140_ = lean_st_ref_get(v_a_2013_);
v_jpParamMask_2141_ = lean_ctor_get(v___x_2140_, 1);
lean_inc_ref(v_jpParamMask_2141_);
lean_dec(v___x_2140_);
v___x_2142_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(v_jpParamMask_2141_, v_fvarId_2118_);
lean_dec_ref(v_jpParamMask_2141_);
v___x_2143_ = lean_unsigned_to_nat(0u);
v___x_2144_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4));
v___x_2145_ = l_Array_zip___redArg(v_args_2119_, v___x_2142_);
lean_dec_ref(v___x_2142_);
lean_dec_ref(v_args_2119_);
v___x_2146_ = lean_array_get_size(v___x_2145_);
v___x_2147_ = lean_nat_dec_lt(v___x_2143_, v___x_2146_);
if (v___x_2147_ == 0)
{
lean_dec_ref(v___x_2145_);
v_a_2124_ = v___x_2144_;
goto v___jp_2123_;
}
else
{
uint8_t v___x_2148_; 
v___x_2148_ = lean_nat_dec_le(v___x_2146_, v___x_2146_);
if (v___x_2148_ == 0)
{
if (v___x_2147_ == 0)
{
lean_dec_ref(v___x_2145_);
v_a_2124_ = v___x_2144_;
goto v___jp_2123_;
}
else
{
size_t v___x_2149_; size_t v___x_2150_; lean_object* v___x_2151_; 
v___x_2149_ = ((size_t)0ULL);
v___x_2150_ = lean_usize_of_nat(v___x_2146_);
v___x_2151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v___x_2145_, v___x_2149_, v___x_2150_, v___x_2144_, v_a_2013_);
lean_dec_ref(v___x_2145_);
v___y_2130_ = v___x_2151_;
goto v___jp_2129_;
}
}
else
{
size_t v___x_2152_; size_t v___x_2153_; lean_object* v___x_2154_; 
v___x_2152_ = ((size_t)0ULL);
v___x_2153_ = lean_usize_of_nat(v___x_2146_);
v___x_2154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v___x_2145_, v___x_2152_, v___x_2153_, v___x_2144_, v_a_2013_);
lean_dec_ref(v___x_2145_);
v___y_2130_ = v___x_2154_;
goto v___jp_2129_;
}
}
v___jp_2123_:
{
lean_object* v___x_2126_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 1, v_a_2124_);
v___x_2126_ = v___x_2121_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_fvarId_2118_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_a_2124_);
v___x_2126_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2127_; 
v___x_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
return v___x_2127_;
}
}
v___jp_2129_:
{
if (lean_obj_tag(v___y_2130_) == 0)
{
lean_object* v_a_2131_; 
v_a_2131_ = lean_ctor_get(v___y_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref(v___y_2130_);
v_a_2124_ = v_a_2131_;
goto v___jp_2123_;
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_del_object(v___x_2121_);
lean_dec(v_fvarId_2118_);
v_a_2132_ = lean_ctor_get(v___y_2130_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___y_2130_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___y_2130_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___y_2130_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
}
}
case 4:
{
lean_object* v_cases_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2266_; 
v_cases_2156_ = lean_ctor_get(v_c_2012_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_c_2012_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2158_ = v_c_2012_;
v_isShared_2159_ = v_isSharedCheck_2266_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_cases_2156_);
lean_dec(v_c_2012_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2266_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v_typeName_2160_; lean_object* v_resultType_2161_; lean_object* v_discr_2162_; lean_object* v_alts_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2265_; 
v_typeName_2160_ = lean_ctor_get(v_cases_2156_, 0);
v_resultType_2161_ = lean_ctor_get(v_cases_2156_, 1);
v_discr_2162_ = lean_ctor_get(v_cases_2156_, 2);
v_alts_2163_ = lean_ctor_get(v_cases_2156_, 3);
v_isSharedCheck_2265_ = !lean_is_exclusive(v_cases_2156_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2165_ = v_cases_2156_;
v_isShared_2166_ = v_isSharedCheck_2265_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_alts_2163_);
lean_inc(v_discr_2162_);
lean_inc(v_resultType_2161_);
lean_inc(v_typeName_2160_);
lean_dec(v_cases_2156_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2265_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2167_; 
lean_inc(v_typeName_2160_);
v___x_2167_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_typeName_2160_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref(v___x_2167_);
if (lean_obj_tag(v_a_2168_) == 1)
{
lean_object* v_val_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; uint8_t v___x_2172_; 
lean_del_object(v___x_2165_);
lean_dec_ref(v_resultType_2161_);
lean_dec(v_typeName_2160_);
lean_del_object(v___x_2158_);
v_val_2169_ = lean_ctor_get(v_a_2168_, 0);
lean_inc(v_val_2169_);
lean_dec_ref(v_a_2168_);
v___x_2170_ = lean_array_get_size(v_alts_2163_);
v___x_2171_ = lean_unsigned_to_nat(1u);
v___x_2172_ = lean_nat_dec_eq(v___x_2170_, v___x_2171_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
lean_dec(v_val_2169_);
lean_dec_ref(v_alts_2163_);
lean_dec(v_discr_2162_);
v___x_2173_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6);
v___x_2174_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2173_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
return v___x_2174_;
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2175_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7);
v___x_2176_ = lean_unsigned_to_nat(0u);
v___x_2177_ = lean_array_get(v___x_2175_, v_alts_2163_, v___x_2176_);
lean_dec_ref(v_alts_2163_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_ctorName_2178_; lean_object* v_params_2179_; lean_object* v_code_2180_; lean_object* v_ctorName_2181_; lean_object* v_fieldIdx_2182_; uint8_t v___x_2183_; 
v_ctorName_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_ctorName_2178_);
v_params_2179_ = lean_ctor_get(v___x_2177_, 1);
lean_inc_ref(v_params_2179_);
v_code_2180_ = lean_ctor_get(v___x_2177_, 2);
lean_inc_ref(v_code_2180_);
lean_dec_ref(v___x_2177_);
v_ctorName_2181_ = lean_ctor_get(v_val_2169_, 0);
lean_inc(v_ctorName_2181_);
v_fieldIdx_2182_ = lean_ctor_get(v_val_2169_, 2);
lean_inc(v_fieldIdx_2182_);
lean_dec(v_val_2169_);
v___x_2183_ = lean_name_eq(v_ctorName_2178_, v_ctorName_2181_);
lean_dec(v_ctorName_2181_);
lean_dec(v_ctorName_2178_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
lean_dec(v_fieldIdx_2182_);
lean_dec_ref(v_code_2180_);
lean_dec_ref(v_params_2179_);
lean_dec(v_discr_2162_);
v___x_2184_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9);
v___x_2185_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2184_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
return v___x_2185_;
}
else
{
lean_object* v___x_2186_; uint8_t v___x_2187_; 
v___x_2186_ = lean_array_get_size(v_params_2179_);
v___x_2187_ = lean_nat_dec_lt(v_fieldIdx_2182_, v___x_2186_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
lean_dec(v_fieldIdx_2182_);
lean_dec_ref(v_code_2180_);
lean_dec_ref(v_params_2179_);
lean_dec(v_discr_2162_);
v___x_2188_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11);
v___x_2189_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2188_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
return v___x_2189_;
}
else
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = lean_box(0);
v___x_2191_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v___x_2186_, v_params_2179_, v_fieldIdx_2182_, v_discr_2162_, v___x_2176_, v___x_2190_, v_a_2013_);
lean_dec(v_fieldIdx_2182_);
lean_dec_ref(v_params_2179_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_dec_ref(v___x_2191_);
v_c_2012_ = v_code_2180_;
goto _start;
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec_ref(v_code_2180_);
v_a_2193_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2191_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2191_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
}
}
else
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_dec(v___x_2177_);
lean_dec(v_val_2169_);
lean_dec(v_discr_2162_);
v___x_2201_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13);
v___x_2202_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2201_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
return v___x_2202_;
}
}
}
else
{
lean_object* v___x_2203_; lean_object* v_subst_2204_; uint8_t v___x_2205_; lean_object* v___x_2206_; 
lean_dec(v_a_2168_);
v___x_2203_ = lean_st_ref_get(v_a_2013_);
v_subst_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc_ref(v_subst_2204_);
lean_dec(v___x_2203_);
v___x_2205_ = 1;
v___x_2206_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_2204_, v_discr_2162_, v___x_2205_);
lean_dec_ref(v_subst_2204_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_fvarId_2207_; lean_object* v___x_2208_; 
v_fvarId_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_fvarId_2207_);
lean_dec_ref(v___x_2206_);
v___x_2208_ = l_Lean_Compiler_LCNF_toImpureType(v_resultType_2161_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; size_t v_sz_2210_; size_t v___x_2211_; lean_object* v___x_2212_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref(v___x_2208_);
v_sz_2210_ = lean_array_size(v_alts_2163_);
v___x_2211_ = ((size_t)0ULL);
lean_inc(v_fvarId_2207_);
v___x_2212_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(v_fvarId_2207_, v_sz_2210_, v___x_2211_, v_alts_2163_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2214_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2213_);
lean_dec_ref(v___x_2212_);
v___x_2214_ = l_Lean_Compiler_LCNF_nameToImpureType(v_typeName_2160_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2230_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2217_ = v___x_2214_;
v_isShared_2218_ = v_isSharedCheck_2230_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2214_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2230_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2219_ = l_Lean_Expr_getAppFn(v_a_2215_);
lean_dec(v_a_2215_);
v___x_2220_ = l_Lean_Expr_constName_x21(v___x_2219_);
lean_dec_ref(v___x_2219_);
if (v_isShared_2166_ == 0)
{
lean_ctor_set(v___x_2165_, 3, v_a_2213_);
lean_ctor_set(v___x_2165_, 2, v_fvarId_2207_);
lean_ctor_set(v___x_2165_, 1, v_a_2209_);
lean_ctor_set(v___x_2165_, 0, v___x_2220_);
v___x_2222_ = v___x_2165_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_a_2209_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_fvarId_2207_);
lean_ctor_set(v_reuseFailAlloc_2229_, 3, v_a_2213_);
v___x_2222_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2224_; 
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v___x_2222_);
v___x_2224_ = v___x_2158_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2226_; 
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 0, v___x_2224_);
v___x_2226_ = v___x_2217_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec(v_a_2213_);
lean_dec(v_a_2209_);
lean_dec(v_fvarId_2207_);
lean_del_object(v___x_2165_);
lean_del_object(v___x_2158_);
v_a_2231_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2214_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2214_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec(v_a_2209_);
lean_dec(v_fvarId_2207_);
lean_del_object(v___x_2165_);
lean_dec(v_typeName_2160_);
lean_del_object(v___x_2158_);
v_a_2239_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2212_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2212_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v_fvarId_2207_);
lean_del_object(v___x_2165_);
lean_dec_ref(v_alts_2163_);
lean_dec(v_typeName_2160_);
lean_del_object(v___x_2158_);
v_a_2247_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2208_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2208_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
else
{
uint8_t v___x_2255_; lean_object* v___x_2256_; 
lean_del_object(v___x_2165_);
lean_dec_ref(v_alts_2163_);
lean_dec_ref(v_resultType_2161_);
lean_dec(v_typeName_2160_);
lean_del_object(v___x_2158_);
v___x_2255_ = 1;
v___x_2256_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_2255_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
return v___x_2256_;
}
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_del_object(v___x_2165_);
lean_dec_ref(v_alts_2163_);
lean_dec(v_discr_2162_);
lean_dec_ref(v_resultType_2161_);
lean_dec(v_typeName_2160_);
lean_del_object(v___x_2158_);
v_a_2257_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2167_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2167_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2288_; 
v_fvarId_2267_ = lean_ctor_get(v_c_2012_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v_c_2012_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2269_ = v_c_2012_;
v_isShared_2270_ = v_isSharedCheck_2288_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_fvarId_2267_);
lean_dec(v_c_2012_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2288_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2271_; lean_object* v_subst_2272_; uint8_t v___x_2273_; lean_object* v___x_2274_; 
v___x_2271_ = lean_st_ref_get(v_a_2013_);
v_subst_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc_ref(v_subst_2272_);
lean_dec(v___x_2271_);
v___x_2273_ = 1;
v___x_2274_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_2272_, v_fvarId_2267_, v___x_2273_);
lean_dec_ref(v_subst_2272_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_fvarId_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2285_; 
v_fvarId_2275_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2277_ = v___x_2274_;
v_isShared_2278_ = v_isSharedCheck_2285_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_fvarId_2275_);
lean_dec(v___x_2274_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2285_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 0, v_fvarId_2275_);
v___x_2280_ = v___x_2269_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_fvarId_2275_);
v___x_2280_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
lean_object* v___x_2282_; 
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v___x_2280_);
v___x_2282_ = v___x_2277_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2280_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
else
{
uint8_t v___x_2286_; lean_object* v___x_2287_; 
lean_del_object(v___x_2269_);
v___x_2286_ = 1;
v___x_2287_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_2286_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
return v___x_2287_;
}
}
}
default: 
{
lean_object* v_type_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2313_; 
v_type_2289_ = lean_ctor_get(v_c_2012_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v_c_2012_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2291_ = v_c_2012_;
v_isShared_2292_ = v_isSharedCheck_2313_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_type_2289_);
lean_dec(v_c_2012_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2313_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Lean_Compiler_LCNF_toImpureType(v_type_2289_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2304_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2304_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2304_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v_a_2294_);
v___x_2299_ = v___x_2291_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
lean_object* v___x_2301_; 
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2299_);
v___x_2301_ = v___x_2296_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2299_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_del_object(v___x_2291_);
v_a_2305_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2293_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2293_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(lean_object* v_decl_2314_, lean_object* v_k_2315_, lean_object* v_ctorInfo_2316_, lean_object* v_fields_2317_, lean_object* v_irArgs_2318_, lean_object* v_i_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_){
_start:
{
lean_object* v___x_2326_; uint8_t v___x_2327_; 
v___x_2326_ = lean_array_get_size(v_irArgs_2318_);
v___x_2327_ = lean_nat_dec_lt(v_i_2319_, v___x_2326_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; 
lean_dec(v_i_2319_);
lean_dec_ref(v_decl_2314_);
v___x_2328_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_2315_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
return v___x_2328_;
}
else
{
lean_object* v___x_2329_; 
v___x_2329_ = lean_array_fget_borrowed(v_irArgs_2318_, v_i_2319_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = lean_unsigned_to_nat(1u);
v___x_2331_ = lean_nat_add(v_i_2319_, v___x_2330_);
lean_dec(v_i_2319_);
v_i_2319_ = v___x_2331_;
goto _start;
}
else
{
lean_object* v_fvarId_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v_fvarId_2333_ = lean_ctor_get(v___x_2329_, 0);
v___x_2334_ = lean_box(0);
v___x_2335_ = lean_array_get_borrowed(v___x_2334_, v_fields_2317_, v_i_2319_);
switch(lean_obj_tag(v___x_2335_))
{
case 1:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = lean_unsigned_to_nat(1u);
v___x_2337_ = lean_nat_add(v_i_2319_, v___x_2336_);
lean_dec(v_i_2319_);
v_i_2319_ = v___x_2337_;
goto _start;
}
case 2:
{
lean_object* v_i_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v_i_2339_ = lean_ctor_get(v___x_2335_, 0);
v___x_2340_ = lean_unsigned_to_nat(1u);
v___x_2341_ = lean_nat_add(v_i_2319_, v___x_2340_);
lean_dec(v_i_2319_);
lean_inc_ref(v_decl_2314_);
v___x_2342_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2314_, v_k_2315_, v_ctorInfo_2316_, v_fields_2317_, v_irArgs_2318_, v___x_2341_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2361_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2361_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2361_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v_fvarId_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2357_; 
v_fvarId_2347_ = lean_ctor_get(v_decl_2314_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v_decl_2314_);
if (v_isSharedCheck_2357_ == 0)
{
lean_object* v_unused_2358_; lean_object* v_unused_2359_; lean_object* v_unused_2360_; 
v_unused_2358_ = lean_ctor_get(v_decl_2314_, 3);
lean_dec(v_unused_2358_);
v_unused_2359_ = lean_ctor_get(v_decl_2314_, 2);
lean_dec(v_unused_2359_);
v_unused_2360_ = lean_ctor_get(v_decl_2314_, 1);
lean_dec(v_unused_2360_);
v___x_2349_ = v_decl_2314_;
v_isShared_2350_ = v_isSharedCheck_2357_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_fvarId_2347_);
lean_dec(v_decl_2314_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2357_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
lean_inc(v_fvarId_2333_);
lean_inc(v_i_2339_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set_tag(v___x_2349_, 8);
lean_ctor_set(v___x_2349_, 3, v_a_2343_);
lean_ctor_set(v___x_2349_, 2, v_fvarId_2333_);
lean_ctor_set(v___x_2349_, 1, v_i_2339_);
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_fvarId_2347_);
lean_ctor_set(v_reuseFailAlloc_2356_, 1, v_i_2339_);
lean_ctor_set(v_reuseFailAlloc_2356_, 2, v_fvarId_2333_);
lean_ctor_set(v_reuseFailAlloc_2356_, 3, v_a_2343_);
v___x_2352_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
lean_object* v___x_2354_; 
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v___x_2352_);
v___x_2354_ = v___x_2345_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
}
else
{
lean_dec_ref(v_decl_2314_);
return v___x_2342_;
}
}
case 3:
{
lean_object* v_offset_2362_; lean_object* v_type_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v_offset_2362_ = lean_ctor_get(v___x_2335_, 1);
v_type_2363_ = lean_ctor_get(v___x_2335_, 2);
v___x_2364_ = lean_unsigned_to_nat(1u);
v___x_2365_ = lean_nat_add(v_i_2319_, v___x_2364_);
lean_dec(v_i_2319_);
lean_inc_ref(v_decl_2314_);
v___x_2366_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2314_, v_k_2315_, v_ctorInfo_2316_, v_fields_2317_, v_irArgs_2318_, v___x_2365_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2379_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2369_ = v___x_2366_;
v_isShared_2370_ = v_isSharedCheck_2379_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2366_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2379_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v_fvarId_2371_; lean_object* v_size_2372_; lean_object* v_usize_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2377_; 
v_fvarId_2371_ = lean_ctor_get(v_decl_2314_, 0);
lean_inc(v_fvarId_2371_);
lean_dec_ref(v_decl_2314_);
v_size_2372_ = lean_ctor_get(v_ctorInfo_2316_, 2);
v_usize_2373_ = lean_ctor_get(v_ctorInfo_2316_, 3);
v___x_2374_ = lean_nat_add(v_size_2372_, v_usize_2373_);
lean_inc_ref(v_type_2363_);
lean_inc(v_fvarId_2333_);
lean_inc(v_offset_2362_);
v___x_2375_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_2375_, 0, v_fvarId_2371_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
lean_ctor_set(v___x_2375_, 2, v_offset_2362_);
lean_ctor_set(v___x_2375_, 3, v_fvarId_2333_);
lean_ctor_set(v___x_2375_, 4, v_type_2363_);
lean_ctor_set(v___x_2375_, 5, v_a_2367_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v___x_2375_);
v___x_2377_ = v___x_2369_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2375_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
else
{
lean_dec_ref(v_decl_2314_);
return v___x_2366_;
}
}
default: 
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = lean_unsigned_to_nat(1u);
v___x_2381_ = lean_nat_add(v_i_2319_, v___x_2380_);
lean_dec(v_i_2319_);
v_i_2319_ = v___x_2381_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(lean_object* v_decl_2383_, lean_object* v_k_2384_, lean_object* v_ctorInfo_2385_, lean_object* v_fields_2386_, lean_object* v_irArgs_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = lean_unsigned_to_nat(0u);
v___x_2395_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2383_, v_k_2384_, v_ctorInfo_2385_, v_fields_2386_, v_irArgs_2387_, v___x_2394_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields___boxed(lean_object* v_decl_2396_, lean_object* v_k_2397_, lean_object* v_ctorInfo_2398_, lean_object* v_fields_2399_, lean_object* v_irArgs_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(v_decl_2396_, v_k_2397_, v_ctorInfo_2398_, v_fields_2399_, v_irArgs_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_);
lean_dec(v_a_2405_);
lean_dec_ref(v_a_2404_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
lean_dec(v_a_2401_);
lean_dec_ref(v_irArgs_2400_);
lean_dec_ref(v_fields_2399_);
lean_dec_ref(v_ctorInfo_2398_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap___boxed(lean_object* v_decl_2408_, lean_object* v_k_2409_, lean_object* v_name_2410_, lean_object* v_args_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(v_decl_2408_, v_k_2409_, v_name_2410_, v_args_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
lean_dec(v_a_2414_);
lean_dec_ref(v_a_2413_);
lean_dec(v_a_2412_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap___boxed(lean_object* v_decl_2419_, lean_object* v_k_2420_, lean_object* v_name_2421_, lean_object* v_args_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_2419_, v_k_2420_, v_name_2421_, v_args_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_);
lean_dec(v_a_2427_);
lean_dec_ref(v_a_2426_);
lean_dec(v_a_2425_);
lean_dec_ref(v_a_2424_);
lean_dec(v_a_2423_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased___boxed(lean_object* v_k_2430_, lean_object* v_fvarId_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_2430_, v_fvarId_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec(v_a_2432_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication___boxed(lean_object* v_decl_2439_, lean_object* v_k_2440_, lean_object* v_name_2441_, lean_object* v_numParams_2442_, lean_object* v_args_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_2439_, v_k_2440_, v_name_2441_, v_numParams_2442_, v_args_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
lean_dec(v_a_2448_);
lean_dec_ref(v_a_2447_);
lean_dec(v_a_2446_);
lean_dec_ref(v_a_2445_);
lean_dec(v_a_2444_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8___boxed(lean_object* v_fvarId_2451_, lean_object* v_sz_2452_, lean_object* v_i_2453_, lean_object* v_bs_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
size_t v_sz_boxed_2461_; size_t v_i_boxed_2462_; lean_object* v_res_2463_; 
v_sz_boxed_2461_ = lean_unbox_usize(v_sz_2452_);
lean_dec(v_sz_2452_);
v_i_boxed_2462_ = lean_unbox_usize(v_i_2453_);
lean_dec(v_i_2453_);
v_res_2463_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(v_fvarId_2451_, v_sz_boxed_2461_, v_i_boxed_2462_, v_bs_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet___boxed(lean_object* v_k_2464_, lean_object* v_decl_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_2464_, v_decl_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
lean_dec(v_a_2470_);
lean_dec_ref(v_a_2469_);
lean_dec(v_a_2468_);
lean_dec_ref(v_a_2467_);
lean_dec(v_a_2466_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure___boxed(lean_object* v_discr_2473_, lean_object* v_alt_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(v_discr_2473_, v_alt_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_);
lean_dec(v_a_2479_);
lean_dec_ref(v_a_2478_);
lean_dec(v_a_2477_);
lean_dec_ref(v_a_2476_);
lean_dec(v_a_2475_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___boxed(lean_object* v_decl_2482_, lean_object* v_k_2483_, lean_object* v_name_2484_, lean_object* v_numParams_2485_, lean_object* v_args_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(v_decl_2482_, v_k_2483_, v_name_2484_, v_numParams_2485_, v_args_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec(v_a_2487_);
lean_dec_ref(v_args_2486_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop___boxed(lean_object* v_decl_2494_, lean_object* v_k_2495_, lean_object* v_ctorInfo_2496_, lean_object* v_fields_2497_, lean_object* v_irArgs_2498_, lean_object* v_i_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2494_, v_k_2495_, v_ctorInfo_2496_, v_fields_2497_, v_irArgs_2498_, v_i_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
lean_dec(v_a_2500_);
lean_dec_ref(v_irArgs_2498_);
lean_dec_ref(v_fields_2497_);
lean_dec_ref(v_ctorInfo_2496_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___boxed(lean_object* v_discr_2507_, lean_object* v_k_2508_, lean_object* v_ctorInfo_2509_, lean_object* v_params_2510_, lean_object* v_fields_2511_, lean_object* v_i_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_2507_, v_k_2508_, v_ctorInfo_2509_, v_params_2510_, v_fields_2511_, v_i_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
lean_dec(v_a_2513_);
lean_dec_ref(v_fields_2511_);
lean_dec_ref(v_params_2510_);
lean_dec_ref(v_ctorInfo_2509_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___boxed(lean_object* v_c_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_c_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec(v_a_2521_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___boxed(lean_object* v_decl_2528_, lean_object* v_k_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(v_decl_2528_, v_k_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
lean_dec(v_a_2534_);
lean_dec_ref(v_a_2533_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
lean_dec(v_a_2530_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(lean_object* v_00_u03b1_2537_, lean_object* v_msg_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_msg_2538_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___boxed(lean_object* v_00_u03b1_2546_, lean_object* v_msg_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(v_00_u03b1_2546_, v_msg_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(size_t v_sz_2555_, size_t v_i_2556_, lean_object* v_bs_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2555_, v_i_2556_, v_bs_2557_, v___y_2558_, v___y_2560_, v___y_2561_, v___y_2562_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___boxed(lean_object* v_sz_2565_, lean_object* v_i_2566_, lean_object* v_bs_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
size_t v_sz_boxed_2574_; size_t v_i_boxed_2575_; lean_object* v_res_2576_; 
v_sz_boxed_2574_ = lean_unbox_usize(v_sz_2565_);
lean_dec(v_sz_2565_);
v_i_boxed_2575_ = lean_unbox_usize(v_i_2566_);
lean_dec(v_i_2566_);
v_res_2576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(v_sz_boxed_2574_, v_i_boxed_2575_, v_bs_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(lean_object* v_as_2577_, size_t v_i_2578_, size_t v_stop_2579_, lean_object* v_b_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v_as_2577_, v_i_2578_, v_stop_2579_, v_b_2580_, v___y_2581_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___boxed(lean_object* v_as_2588_, lean_object* v_i_2589_, lean_object* v_stop_2590_, lean_object* v_b_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
size_t v_i_boxed_2598_; size_t v_stop_boxed_2599_; lean_object* v_res_2600_; 
v_i_boxed_2598_ = lean_unbox_usize(v_i_2589_);
lean_dec(v_i_2589_);
v_stop_boxed_2599_ = lean_unbox_usize(v_stop_2590_);
lean_dec(v_stop_2590_);
v_res_2600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(v_as_2588_, v_i_boxed_2598_, v_stop_boxed_2599_, v_b_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v_as_2588_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(lean_object* v_upperBound_2601_, lean_object* v_params_2602_, lean_object* v___x_2603_, lean_object* v_discr_2604_, lean_object* v_inst_2605_, lean_object* v_R_2606_, lean_object* v_a_2607_, lean_object* v_b_2608_, lean_object* v_c_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v_upperBound_2601_, v_params_2602_, v___x_2603_, v_discr_2604_, v_a_2607_, v_b_2608_, v___y_2610_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___boxed(lean_object* v_upperBound_2617_, lean_object* v_params_2618_, lean_object* v___x_2619_, lean_object* v_discr_2620_, lean_object* v_inst_2621_, lean_object* v_R_2622_, lean_object* v_a_2623_, lean_object* v_b_2624_, lean_object* v_c_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(v_upperBound_2617_, v_params_2618_, v___x_2619_, v_discr_2620_, v_inst_2621_, v_R_2622_, v_a_2623_, v_b_2624_, v_c_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec(v___x_2619_);
lean_dec_ref(v_params_2618_);
lean_dec(v_upperBound_2617_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11(size_t v_sz_2633_, size_t v_i_2634_, lean_object* v_bs_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_2633_, v_i_2634_, v_bs_2635_, v___y_2636_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___boxed(lean_object* v_sz_2643_, lean_object* v_i_2644_, lean_object* v_bs_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
size_t v_sz_boxed_2652_; size_t v_i_boxed_2653_; lean_object* v_res_2654_; 
v_sz_boxed_2652_ = lean_unbox_usize(v_sz_2643_);
lean_dec(v_sz_2643_);
v_i_boxed_2653_ = lean_unbox_usize(v_i_2644_);
lean_dec(v_i_2644_);
v_res_2654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11(v_sz_boxed_2652_, v_i_boxed_2653_, v_bs_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(lean_object* v_upperBound_2655_, lean_object* v_fieldInfo_2656_, lean_object* v___x_2657_, lean_object* v_inst_2658_, lean_object* v_R_2659_, lean_object* v_a_2660_, lean_object* v_b_2661_, lean_object* v_c_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v_upperBound_2655_, v_fieldInfo_2656_, v___x_2657_, v_a_2660_, v_b_2661_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___boxed(lean_object* v_upperBound_2670_, lean_object* v_fieldInfo_2671_, lean_object* v___x_2672_, lean_object* v_inst_2673_, lean_object* v_R_2674_, lean_object* v_a_2675_, lean_object* v_b_2676_, lean_object* v_c_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(v_upperBound_2670_, v_fieldInfo_2671_, v___x_2672_, v_inst_2673_, v_R_2674_, v_a_2675_, v_b_2676_, v_c_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec(v___y_2678_);
lean_dec_ref(v___x_2672_);
lean_dec_ref(v_fieldInfo_2671_);
lean_dec(v_upperBound_2670_);
return v_res_2684_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1(void){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2686_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0));
v___x_2687_ = l_Lean_stringToMessageData(v___x_2686_);
return v___x_2687_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3(void){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2689_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2));
v___x_2690_ = l_Lean_stringToMessageData(v___x_2689_);
return v___x_2690_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5(void){
_start:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2692_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4));
v___x_2693_ = l_Lean_stringToMessageData(v___x_2692_);
return v___x_2693_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7(void){
_start:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2695_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6));
v___x_2696_ = l_Lean_stringToMessageData(v___x_2695_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(lean_object* v_decl_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_){
_start:
{
lean_object* v_toSignature_2704_; lean_object* v_value_2705_; uint8_t v_recursive_2706_; lean_object* v_inlineAttr_x3f_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2839_; 
v_toSignature_2704_ = lean_ctor_get(v_decl_2697_, 0);
v_value_2705_ = lean_ctor_get(v_decl_2697_, 1);
v_recursive_2706_ = lean_ctor_get_uint8(v_decl_2697_, sizeof(void*)*3);
v_inlineAttr_x3f_2707_ = lean_ctor_get(v_decl_2697_, 2);
v_isSharedCheck_2839_ = !lean_is_exclusive(v_decl_2697_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2709_ = v_decl_2697_;
v_isShared_2710_ = v_isSharedCheck_2839_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_inlineAttr_x3f_2707_);
lean_inc(v_value_2705_);
lean_inc(v_toSignature_2704_);
lean_dec(v_decl_2697_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2839_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v_name_2711_; lean_object* v_levelParams_2712_; lean_object* v_type_2713_; lean_object* v_params_2714_; uint8_t v_safe_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2838_; 
v_name_2711_ = lean_ctor_get(v_toSignature_2704_, 0);
v_levelParams_2712_ = lean_ctor_get(v_toSignature_2704_, 1);
v_type_2713_ = lean_ctor_get(v_toSignature_2704_, 2);
v_params_2714_ = lean_ctor_get(v_toSignature_2704_, 3);
v_safe_2715_ = lean_ctor_get_uint8(v_toSignature_2704_, sizeof(void*)*4);
v_isSharedCheck_2838_ = !lean_is_exclusive(v_toSignature_2704_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2717_ = v_toSignature_2704_;
v_isShared_2718_ = v_isSharedCheck_2838_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_params_2714_);
lean_inc(v_type_2713_);
lean_inc(v_levelParams_2712_);
lean_inc(v_name_2711_);
lean_dec(v_toSignature_2704_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2838_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
size_t v_sz_2719_; size_t v___x_2720_; lean_object* v___x_2721_; 
v_sz_2719_ = lean_array_size(v_params_2714_);
v___x_2720_ = ((size_t)0ULL);
lean_inc_ref(v_params_2714_);
v___x_2721_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2719_, v___x_2720_, v_params_2714_, v_a_2698_, v_a_2700_, v_a_2701_, v_a_2702_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_a_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_a_2722_);
lean_dec_ref(v___x_2721_);
v___x_2723_ = lean_array_get_size(v_params_2714_);
lean_dec_ref(v_params_2714_);
v___x_2724_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_2713_, v___x_2723_, v_a_2701_, v_a_2702_);
lean_dec_ref(v_type_2713_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2821_; 
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2727_ = v___x_2724_;
v_isShared_2728_ = v_isSharedCheck_2821_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2724_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2821_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2729_; lean_object* v_env_2730_; lean_object* v___x_2731_; uint8_t v___x_2732_; 
v___x_2729_ = lean_st_ref_get(v_a_2702_);
v_env_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc_ref(v_env_2730_);
lean_dec(v___x_2729_);
v___x_2731_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr;
lean_inc(v_name_2711_);
v___x_2732_ = l_Lean_TagAttribute_hasTag(v___x_2731_, v_env_2730_, v_name_2711_);
if (lean_obj_tag(v_value_2705_) == 0)
{
lean_object* v_code_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2783_; 
lean_del_object(v___x_2727_);
v_code_2733_ = lean_ctor_get(v_value_2705_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_value_2705_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2735_ = v_value_2705_;
v_isShared_2736_ = v_isSharedCheck_2783_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_code_2733_);
lean_dec(v_value_2705_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2783_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v___y_2742_; 
if (v___x_2732_ == 0)
{
v___y_2738_ = v_a_2698_;
v___y_2739_ = v_a_2699_;
v___y_2740_ = v_a_2700_;
v___y_2741_ = v_a_2701_;
v___y_2742_ = v_a_2702_;
goto v___jp_2737_;
}
else
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_del_object(v___x_2735_);
lean_dec_ref(v_code_2733_);
lean_dec(v_a_2725_);
lean_dec(v_a_2722_);
lean_del_object(v___x_2717_);
lean_dec(v_levelParams_2712_);
lean_del_object(v___x_2709_);
lean_dec(v_inlineAttr_x3f_2707_);
v___x_2769_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1);
v___x_2770_ = l_Lean_MessageData_ofName(v_name_2711_);
v___x_2771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2769_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
v___x_2772_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3);
v___x_2773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2771_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
v___x_2774_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_2773_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2774_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2774_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
v___jp_2737_:
{
lean_object* v___x_2743_; 
v___x_2743_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_code_2733_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2760_; 
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2746_ = v___x_2743_;
v_isShared_2747_ = v_isSharedCheck_2760_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2743_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2760_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 3, v_a_2722_);
lean_ctor_set(v___x_2717_, 2, v_a_2725_);
v___x_2749_ = v___x_2717_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_name_2711_);
lean_ctor_set(v_reuseFailAlloc_2759_, 1, v_levelParams_2712_);
lean_ctor_set(v_reuseFailAlloc_2759_, 2, v_a_2725_);
lean_ctor_set(v_reuseFailAlloc_2759_, 3, v_a_2722_);
lean_ctor_set_uint8(v_reuseFailAlloc_2759_, sizeof(void*)*4, v_safe_2715_);
v___x_2749_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_object* v___x_2751_; 
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 0, v_a_2744_);
v___x_2751_ = v___x_2735_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2744_);
v___x_2751_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
lean_object* v___x_2753_; 
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 1, v___x_2751_);
lean_ctor_set(v___x_2709_, 0, v___x_2749_);
v___x_2753_ = v___x_2709_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2749_);
lean_ctor_set(v_reuseFailAlloc_2757_, 1, v___x_2751_);
lean_ctor_set(v_reuseFailAlloc_2757_, 2, v_inlineAttr_x3f_2707_);
lean_ctor_set_uint8(v_reuseFailAlloc_2757_, sizeof(void*)*3, v_recursive_2706_);
v___x_2753_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
lean_object* v___x_2755_; 
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 0, v___x_2753_);
v___x_2755_ = v___x_2746_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2753_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_del_object(v___x_2735_);
lean_dec(v_a_2725_);
lean_dec(v_a_2722_);
lean_del_object(v___x_2717_);
lean_dec(v_levelParams_2712_);
lean_dec(v_name_2711_);
lean_del_object(v___x_2709_);
lean_dec(v_inlineAttr_x3f_2707_);
v_a_2761_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2743_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2743_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
}
}
else
{
lean_object* v_externAttrData_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2820_; 
v_externAttrData_2784_ = lean_ctor_get(v_value_2705_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v_value_2705_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2786_ = v_value_2705_;
v_isShared_2787_ = v_isSharedCheck_2820_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_externAttrData_2784_);
lean_dec(v_value_2705_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2820_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v_resultType_2789_; 
if (v___x_2732_ == 0)
{
v_resultType_2789_ = v_a_2725_;
goto v___jp_2788_;
}
else
{
uint8_t v___x_2802_; 
v___x_2802_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_2725_);
if (v___x_2802_ == 0)
{
lean_object* v___x_2803_; 
lean_dec(v_a_2725_);
v___x_2803_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5);
v_resultType_2789_ = v___x_2803_;
goto v___jp_2788_;
}
else
{
lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_del_object(v___x_2786_);
lean_dec(v_externAttrData_2784_);
lean_del_object(v___x_2727_);
lean_dec(v_a_2722_);
lean_del_object(v___x_2717_);
lean_dec(v_levelParams_2712_);
lean_del_object(v___x_2709_);
lean_dec(v_inlineAttr_x3f_2707_);
v___x_2804_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5);
v___x_2805_ = l_Lean_MessageData_ofName(v_name_2711_);
v___x_2806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2804_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
v___x_2807_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7);
v___x_2808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2806_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
v___x_2809_ = l_Lean_MessageData_ofExpr(v_a_2725_);
v___x_2810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2808_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
v___x_2811_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_2810_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2811_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
v___jp_2788_:
{
lean_object* v___x_2791_; 
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 3, v_a_2722_);
lean_ctor_set(v___x_2717_, 2, v_resultType_2789_);
v___x_2791_ = v___x_2717_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_name_2711_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v_levelParams_2712_);
lean_ctor_set(v_reuseFailAlloc_2801_, 2, v_resultType_2789_);
lean_ctor_set(v_reuseFailAlloc_2801_, 3, v_a_2722_);
lean_ctor_set_uint8(v_reuseFailAlloc_2801_, sizeof(void*)*4, v_safe_2715_);
v___x_2791_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
lean_object* v___x_2793_; 
if (v_isShared_2787_ == 0)
{
v___x_2793_ = v___x_2786_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_externAttrData_2784_);
v___x_2793_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2795_; 
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 1, v___x_2793_);
lean_ctor_set(v___x_2709_, 0, v___x_2791_);
v___x_2795_ = v___x_2709_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2791_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v___x_2793_);
lean_ctor_set(v_reuseFailAlloc_2799_, 2, v_inlineAttr_x3f_2707_);
lean_ctor_set_uint8(v_reuseFailAlloc_2799_, sizeof(void*)*3, v_recursive_2706_);
v___x_2795_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2797_; 
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 0, v___x_2795_);
v___x_2797_ = v___x_2727_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2795_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_dec(v_a_2722_);
lean_del_object(v___x_2717_);
lean_dec(v_levelParams_2712_);
lean_dec(v_name_2711_);
lean_del_object(v___x_2709_);
lean_dec(v_inlineAttr_x3f_2707_);
lean_dec_ref(v_value_2705_);
v_a_2822_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2724_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2724_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
else
{
lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_del_object(v___x_2717_);
lean_dec_ref(v_params_2714_);
lean_dec_ref(v_type_2713_);
lean_dec(v_levelParams_2712_);
lean_dec(v_name_2711_);
lean_del_object(v___x_2709_);
lean_dec(v_inlineAttr_x3f_2707_);
lean_dec_ref(v_value_2705_);
v_a_2830_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2721_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2721_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___boxed(lean_object* v_decl_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(v_decl_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_);
lean_dec(v_a_2845_);
lean_dec_ref(v_a_2844_);
lean_dec(v_a_2843_);
lean_dec_ref(v_a_2842_);
lean_dec(v_a_2841_);
return v_res_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(lean_object* v_decl_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(v_decl_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2857_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc_n(v_a_2856_, 2);
lean_dec_ref(v___x_2855_);
v___x_2857_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_a_2856_, v_a_2853_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2864_ == 0)
{
lean_object* v_unused_2865_; 
v_unused_2865_ = lean_ctor_get(v___x_2857_, 0);
lean_dec(v_unused_2865_);
v___x_2859_ = v___x_2857_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_dec(v___x_2857_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v_a_2856_);
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2856_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec(v_a_2856_);
v_a_2866_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2857_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2857_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
else
{
return v___x_2855_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go___boxed(lean_object* v_decl_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(v_decl_2874_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_);
lean_dec(v_a_2879_);
lean_dec_ref(v_a_2878_);
lean_dec(v_a_2877_);
lean_dec_ref(v_a_2876_);
lean_dec(v_a_2875_);
return v_res_2881_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0(void){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2882_ = lean_box(0);
v___x_2883_ = lean_unsigned_to_nat(16u);
v___x_2884_ = lean_mk_array(v___x_2883_, v___x_2882_);
return v___x_2884_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1(void){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2885_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0);
v___x_2886_ = lean_unsigned_to_nat(0u);
v___x_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
lean_ctor_set(v___x_2887_, 1, v___x_2885_);
return v___x_2887_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2(void){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2888_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1);
v___x_2889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2888_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(lean_object* v_decl_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2896_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2);
v___x_2897_ = lean_st_mk_ref(v___x_2896_);
v___x_2898_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(v_decl_2890_, v___x_2897_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2907_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2901_ = v___x_2898_;
v_isShared_2902_ = v_isSharedCheck_2907_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2898_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2907_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2903_; lean_object* v___x_2905_; 
v___x_2903_ = lean_st_ref_get(v___x_2897_);
lean_dec(v___x_2897_);
lean_dec(v___x_2903_);
if (v_isShared_2902_ == 0)
{
v___x_2905_ = v___x_2901_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2899_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
else
{
lean_dec(v___x_2897_);
return v___x_2898_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___boxed(lean_object* v_decl_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(v_decl_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
lean_dec(v_a_2910_);
lean_dec_ref(v_a_2909_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(size_t v_sz_2915_, size_t v_i_2916_, lean_object* v_bs_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
uint8_t v___x_2923_; 
v___x_2923_ = lean_usize_dec_lt(v_i_2916_, v_sz_2915_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; 
v___x_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2924_, 0, v_bs_2917_);
return v___x_2924_;
}
else
{
lean_object* v_v_2925_; lean_object* v___x_2926_; 
v_v_2925_ = lean_array_uget_borrowed(v_bs_2917_, v_i_2916_);
lean_inc(v_v_2925_);
v___x_2926_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(v_v_2925_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v___x_2928_; lean_object* v_bs_x27_2929_; size_t v___x_2930_; size_t v___x_2931_; lean_object* v___x_2932_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
lean_dec_ref(v___x_2926_);
v___x_2928_ = lean_unsigned_to_nat(0u);
v_bs_x27_2929_ = lean_array_uset(v_bs_2917_, v_i_2916_, v___x_2928_);
v___x_2930_ = ((size_t)1ULL);
v___x_2931_ = lean_usize_add(v_i_2916_, v___x_2930_);
v___x_2932_ = lean_array_uset(v_bs_x27_2929_, v_i_2916_, v_a_2927_);
v_i_2916_ = v___x_2931_;
v_bs_2917_ = v___x_2932_;
goto _start;
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec_ref(v_bs_2917_);
v_a_2934_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2926_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2926_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0___boxed(lean_object* v_sz_2942_, lean_object* v_i_2943_, lean_object* v_bs_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
size_t v_sz_boxed_2950_; size_t v_i_boxed_2951_; lean_object* v_res_2952_; 
v_sz_boxed_2950_ = lean_unbox_usize(v_sz_2942_);
lean_dec(v_sz_2942_);
v_i_boxed_2951_ = lean_unbox_usize(v_i_2943_);
lean_dec(v_i_2943_);
v_res_2952_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(v_sz_boxed_2950_, v_i_boxed_2951_, v_bs_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0(lean_object* v_x_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
size_t v_sz_2959_; size_t v___x_2960_; lean_object* v___x_2961_; 
v_sz_2959_ = lean_array_size(v_x_2953_);
v___x_2960_ = ((size_t)0ULL);
v___x_2961_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(v_sz_2959_, v___x_2960_, v_x_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0___boxed(lean_object* v_x_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_Compiler_LCNF_toImpure___lam__0(v_x_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3019_; uint8_t v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3019_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_));
v___x_3020_ = 1;
v___x_3021_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_));
v___x_3022_ = l_Lean_registerTraceClass(v___x_3019_, v___x_3020_, v___x_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2____boxed(lean_object* v_a_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_();
return v_res_3024_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_ToImpureType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ToImpure(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr);
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue = _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue);
res = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ToImpure(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_ToImpureType(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ToImpure(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ToImpure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ToImpure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ToImpure(builtin);
}
#ifdef __cplusplus
}
#endif
