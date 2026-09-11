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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tagged_return"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(42, 116, 83, 63, 133, 144, 27, 22)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "mark extern definition to always return tagged values"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 25, 15, 1, 146, 18, 87, 58)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ToImpure"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(104, 151, 203, 144, 27, 18, 236, 68)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(65, 46, 141, 239, 133, 91, 141, 199)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(228, 234, 69, 211, 145, 232, 229, 254)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(78, 187, 249, 147, 190, 91, 90, 40)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(183, 4, 28, 224, 230, 52, 114, 252)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "taggedReturnAttr"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(243, 95, 219, 231, 93, 109, 209, 250)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 150, .m_capacity = 150, .m_length = 149, .m_data = "Marks an extern definition to be guaranteed to always return tagged values.\nThis information is used to optimize reference counting in the compiler.\n"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(18) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1)),((lean_object*)(((size_t)(93) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(93) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(23) << 1) | 1)),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__4_value),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___boxed(lean_object*);
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
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 55, 142, 128, 91, 63, 88, 28)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_toImpure___closed__1_value),LEAN_SCALAR_PTR_LITERAL(198, 36, 7, 136, 133, 159, 176, 55)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 198, 164, 214, 24, 238, 231, 213)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(55, 168, 178, 247, 202, 119, 73, 243)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(202, 77, 105, 21, 218, 121, 239, 197)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 184, 169, 248, 178, 143, 79, 195)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 14, 162, 97, 10, 113, 167, 163)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(88, 160, 236, 105, 16, 144, 54, 23)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_box(0);
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed(lean_object* v_x_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(v_x_7_, v___y_8_, v___y_9_);
lean_dec(v___y_9_);
lean_dec_ref(v___y_8_);
lean_dec(v_x_7_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; uint8_t v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___f_54_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_55_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_56_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_57_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_58_ = 0;
v___x_59_ = lean_box(2);
v___x_60_ = l_Lean_registerTagAttribute(v___x_55_, v___x_56_, v___f_54_, v___x_57_, v___x_58_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2____boxed(lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_();
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1(){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_66_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___closed__0));
v___x_67_ = l_Lean_addBuiltinDocString(v___x_65_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1___boxed(lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1();
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3(){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_));
v___x_97_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___closed__6));
v___x_98_ = l_Lean_addBuiltinDeclarationRanges(v___x_96_, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3___boxed(lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3();
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0(lean_object* v_____do__lift_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_subst_108_; lean_object* v___x_109_; 
v_subst_108_ = lean_ctor_get(v_____do__lift_101_, 0);
lean_inc_ref(v_subst_108_);
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v_subst_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0___boxed(lean_object* v_____do__lift_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___lam__0(v_____do__lift_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v_____do__lift_110_);
return v_res_117_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0(void){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_instMonadEIO(lean_box(0));
return v___x_118_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__0);
v___x_120_ = l_StateRefT_x27_instMonad___redArg(v___x_119_);
return v___x_120_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue(void){
_start:
{
lean_object* v___x_149_; lean_object* v_toApplicative_150_; lean_object* v_toFunctor_151_; lean_object* v_toSeq_152_; lean_object* v_toSeqLeft_153_; lean_object* v_toSeqRight_154_; lean_object* v___f_155_; lean_object* v___f_156_; lean_object* v___f_157_; lean_object* v___f_158_; lean_object* v___x_159_; lean_object* v___f_160_; lean_object* v___f_161_; lean_object* v___f_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v_toApplicative_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_196_; 
v___x_149_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1);
v_toApplicative_150_ = lean_ctor_get(v___x_149_, 0);
v_toFunctor_151_ = lean_ctor_get(v_toApplicative_150_, 0);
v_toSeq_152_ = lean_ctor_get(v_toApplicative_150_, 2);
v_toSeqLeft_153_ = lean_ctor_get(v_toApplicative_150_, 3);
v_toSeqRight_154_ = lean_ctor_get(v_toApplicative_150_, 4);
v___f_155_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2));
v___f_156_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3));
lean_inc_ref_n(v_toFunctor_151_, 2);
v___f_157_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_157_, 0, v_toFunctor_151_);
v___f_158_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_158_, 0, v_toFunctor_151_);
v___x_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_159_, 0, v___f_157_);
lean_ctor_set(v___x_159_, 1, v___f_158_);
lean_inc(v_toSeqRight_154_);
v___f_160_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_160_, 0, v_toSeqRight_154_);
lean_inc(v_toSeqLeft_153_);
v___f_161_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_161_, 0, v_toSeqLeft_153_);
lean_inc(v_toSeq_152_);
v___f_162_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_162_, 0, v_toSeq_152_);
v___x_163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_163_, 0, v___x_159_);
lean_ctor_set(v___x_163_, 1, v___f_155_);
lean_ctor_set(v___x_163_, 2, v___f_162_);
lean_ctor_set(v___x_163_, 3, v___f_161_);
lean_ctor_set(v___x_163_, 4, v___f_160_);
v___x_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___f_156_);
v___x_165_ = l_StateRefT_x27_instMonad___redArg(v___x_164_);
v_toApplicative_166_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_196_ == 0)
{
lean_object* v_unused_197_; 
v_unused_197_ = lean_ctor_get(v___x_165_, 1);
lean_dec(v_unused_197_);
v___x_168_ = v___x_165_;
v_isShared_169_ = v_isSharedCheck_196_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_toApplicative_166_);
lean_dec(v___x_165_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_196_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v_toFunctor_170_; lean_object* v_toSeq_171_; lean_object* v_toSeqLeft_172_; lean_object* v_toSeqRight_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_194_; 
v_toFunctor_170_ = lean_ctor_get(v_toApplicative_166_, 0);
v_toSeq_171_ = lean_ctor_get(v_toApplicative_166_, 2);
v_toSeqLeft_172_ = lean_ctor_get(v_toApplicative_166_, 3);
v_toSeqRight_173_ = lean_ctor_get(v_toApplicative_166_, 4);
v_isSharedCheck_194_ = !lean_is_exclusive(v_toApplicative_166_);
if (v_isSharedCheck_194_ == 0)
{
lean_object* v_unused_195_; 
v_unused_195_ = lean_ctor_get(v_toApplicative_166_, 1);
lean_dec(v_unused_195_);
v___x_175_ = v_toApplicative_166_;
v_isShared_176_ = v_isSharedCheck_194_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_toSeqRight_173_);
lean_inc(v_toSeqLeft_172_);
lean_inc(v_toSeq_171_);
lean_inc(v_toFunctor_170_);
lean_dec(v_toApplicative_166_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_194_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___f_177_; lean_object* v___f_178_; lean_object* v___f_179_; lean_object* v___f_180_; lean_object* v___f_181_; lean_object* v___x_182_; lean_object* v___f_183_; lean_object* v___f_184_; lean_object* v___f_185_; lean_object* v___x_187_; 
v___f_177_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__4));
v___f_178_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5));
v___f_179_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6));
lean_inc_ref(v_toFunctor_170_);
v___f_180_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_180_, 0, v_toFunctor_170_);
v___f_181_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_181_, 0, v_toFunctor_170_);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v___f_180_);
lean_ctor_set(v___x_182_, 1, v___f_181_);
v___f_183_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_183_, 0, v_toSeqRight_173_);
v___f_184_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_184_, 0, v_toSeqLeft_172_);
v___f_185_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_185_, 0, v_toSeq_171_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 4, v___f_183_);
lean_ctor_set(v___x_175_, 3, v___f_184_);
lean_ctor_set(v___x_175_, 2, v___f_185_);
lean_ctor_set(v___x_175_, 1, v___f_178_);
lean_ctor_set(v___x_175_, 0, v___x_182_);
v___x_187_ = v___x_175_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v___f_178_);
lean_ctor_set(v_reuseFailAlloc_193_, 2, v___f_185_);
lean_ctor_set(v_reuseFailAlloc_193_, 3, v___f_184_);
lean_ctor_set(v_reuseFailAlloc_193_, 4, v___f_183_);
v___x_187_ = v_reuseFailAlloc_193_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_189_; 
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 1, v___f_179_);
lean_ctor_set(v___x_168_, 0, v___x_187_);
v___x_189_ = v___x_168_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v___f_179_);
v___x_189_ = v_reuseFailAlloc_192_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__18));
v___x_191_ = lean_alloc_closure((void*)(l_ReaderT_bind___boxed), 8, 7);
lean_closure_set(v___x_191_, 0, lean_box(0));
lean_closure_set(v___x_191_, 1, lean_box(0));
lean_closure_set(v___x_191_, 2, v___x_189_);
lean_closure_set(v___x_191_, 3, lean_box(0));
lean_closure_set(v___x_191_, 4, lean_box(0));
lean_closure_set(v___x_191_, 5, v___x_190_);
lean_closure_set(v___x_191_, 6, v___f_177_);
return v___x_191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0(lean_object* v_f_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v___x_205_; lean_object* v_subst_206_; lean_object* v_jpParamMask_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_218_; 
v___x_205_ = lean_st_ref_take(v___y_199_);
v_subst_206_ = lean_ctor_get(v___x_205_, 0);
v_jpParamMask_207_ = lean_ctor_get(v___x_205_, 1);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_218_ == 0)
{
v___x_209_ = v___x_205_;
v_isShared_210_ = v_isSharedCheck_218_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_jpParamMask_207_);
lean_inc(v_subst_206_);
lean_dec(v___x_205_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_218_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = lean_apply_1(v_f_198_, v_subst_206_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v___x_211_);
v___x_213_ = v___x_209_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_211_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_jpParamMask_207_);
v___x_213_ = v_reuseFailAlloc_217_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_214_ = lean_st_ref_put(v___y_199_, v___x_213_);
v___x_215_ = lean_box(0);
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
return v___x_216_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0___boxed(lean_object* v_f_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstStateToImpureMPure___lam__0(v_f_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(lean_object* v_a_229_, lean_object* v_b_230_, lean_object* v_x_231_){
_start:
{
if (lean_obj_tag(v_x_231_) == 0)
{
lean_dec(v_b_230_);
lean_dec(v_a_229_);
return v_x_231_;
}
else
{
lean_object* v_key_232_; lean_object* v_value_233_; lean_object* v_tail_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_246_; 
v_key_232_ = lean_ctor_get(v_x_231_, 0);
v_value_233_ = lean_ctor_get(v_x_231_, 1);
v_tail_234_ = lean_ctor_get(v_x_231_, 2);
v_isSharedCheck_246_ = !lean_is_exclusive(v_x_231_);
if (v_isSharedCheck_246_ == 0)
{
v___x_236_ = v_x_231_;
v_isShared_237_ = v_isSharedCheck_246_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_tail_234_);
lean_inc(v_value_233_);
lean_inc(v_key_232_);
lean_dec(v_x_231_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_246_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
uint8_t v___x_238_; 
v___x_238_ = l_Lean_instBEqFVarId_beq(v_key_232_, v_a_229_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_229_, v_b_230_, v_tail_234_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 2, v___x_239_);
v___x_241_ = v___x_236_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_key_232_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_value_233_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
else
{
lean_object* v___x_244_; 
lean_dec(v_value_233_);
lean_dec(v_key_232_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 1, v_b_230_);
lean_ctor_set(v___x_236_, 0, v_a_229_);
v___x_244_ = v___x_236_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_229_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_b_230_);
lean_ctor_set(v_reuseFailAlloc_245_, 2, v_tail_234_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
if (lean_obj_tag(v_x_248_) == 0)
{
return v_x_247_;
}
else
{
lean_object* v_key_249_; lean_object* v_value_250_; lean_object* v_tail_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_274_; 
v_key_249_ = lean_ctor_get(v_x_248_, 0);
v_value_250_ = lean_ctor_get(v_x_248_, 1);
v_tail_251_ = lean_ctor_get(v_x_248_, 2);
v_isSharedCheck_274_ = !lean_is_exclusive(v_x_248_);
if (v_isSharedCheck_274_ == 0)
{
v___x_253_ = v_x_248_;
v_isShared_254_ = v_isSharedCheck_274_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_tail_251_);
lean_inc(v_value_250_);
lean_inc(v_key_249_);
lean_dec(v_x_248_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_274_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; uint64_t v___x_256_; uint64_t v___x_257_; uint64_t v___x_258_; uint64_t v_fold_259_; uint64_t v___x_260_; uint64_t v___x_261_; uint64_t v___x_262_; size_t v___x_263_; size_t v___x_264_; size_t v___x_265_; size_t v___x_266_; size_t v___x_267_; lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_255_ = lean_array_get_size(v_x_247_);
v___x_256_ = l_Lean_instHashableFVarId_hash(v_key_249_);
v___x_257_ = 32ULL;
v___x_258_ = lean_uint64_shift_right(v___x_256_, v___x_257_);
v_fold_259_ = lean_uint64_xor(v___x_256_, v___x_258_);
v___x_260_ = 16ULL;
v___x_261_ = lean_uint64_shift_right(v_fold_259_, v___x_260_);
v___x_262_ = lean_uint64_xor(v_fold_259_, v___x_261_);
v___x_263_ = lean_uint64_to_usize(v___x_262_);
v___x_264_ = lean_usize_of_nat(v___x_255_);
v___x_265_ = ((size_t)1ULL);
v___x_266_ = lean_usize_sub(v___x_264_, v___x_265_);
v___x_267_ = lean_usize_land(v___x_263_, v___x_266_);
v___x_268_ = lean_array_uget_borrowed(v_x_247_, v___x_267_);
lean_inc(v___x_268_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 2, v___x_268_);
v___x_270_ = v___x_253_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_key_249_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_value_250_);
lean_ctor_set(v_reuseFailAlloc_273_, 2, v___x_268_);
v___x_270_ = v_reuseFailAlloc_273_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
lean_object* v___x_271_; 
v___x_271_ = lean_array_uset(v_x_247_, v___x_267_, v___x_270_);
v_x_247_ = v___x_271_;
v_x_248_ = v_tail_251_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(lean_object* v_i_275_, lean_object* v_source_276_, lean_object* v_target_277_){
_start:
{
lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_278_ = lean_array_get_size(v_source_276_);
v___x_279_ = lean_nat_dec_lt(v_i_275_, v___x_278_);
if (v___x_279_ == 0)
{
lean_dec_ref(v_source_276_);
lean_dec(v_i_275_);
return v_target_277_;
}
else
{
lean_object* v_es_280_; lean_object* v___x_281_; lean_object* v_source_282_; lean_object* v_target_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_es_280_ = lean_array_fget(v_source_276_, v_i_275_);
v___x_281_ = lean_box(0);
v_source_282_ = lean_array_fset(v_source_276_, v_i_275_, v___x_281_);
v_target_283_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(v_target_277_, v_es_280_);
v___x_284_ = lean_unsigned_to_nat(1u);
v___x_285_ = lean_nat_add(v_i_275_, v___x_284_);
lean_dec(v_i_275_);
v_i_275_ = v___x_285_;
v_source_276_ = v_source_282_;
v_target_277_ = v_target_283_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(lean_object* v_data_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v_nbuckets_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_288_ = lean_array_get_size(v_data_287_);
v___x_289_ = lean_unsigned_to_nat(2u);
v_nbuckets_290_ = lean_nat_mul(v___x_288_, v___x_289_);
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = lean_box(0);
v___x_293_ = lean_mk_array(v_nbuckets_290_, v___x_292_);
v___x_294_ = lean_array_propagate_mark(v_data_287_, v___x_293_);
v___x_295_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(v___x_291_, v_data_287_, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(lean_object* v_a_296_, lean_object* v_x_297_){
_start:
{
if (lean_obj_tag(v_x_297_) == 0)
{
uint8_t v___x_298_; 
v___x_298_ = 0;
return v___x_298_;
}
else
{
lean_object* v_key_299_; lean_object* v_tail_300_; uint8_t v___x_301_; 
v_key_299_ = lean_ctor_get(v_x_297_, 0);
v_tail_300_ = lean_ctor_get(v_x_297_, 2);
v___x_301_ = l_Lean_instBEqFVarId_beq(v_key_299_, v_a_296_);
if (v___x_301_ == 0)
{
v_x_297_ = v_tail_300_;
goto _start;
}
else
{
return v___x_301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg___boxed(lean_object* v_a_303_, lean_object* v_x_304_){
_start:
{
uint8_t v_res_305_; lean_object* v_r_306_; 
v_res_305_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_303_, v_x_304_);
lean_dec(v_x_304_);
lean_dec(v_a_303_);
v_r_306_ = lean_box(v_res_305_);
return v_r_306_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(lean_object* v_m_307_, lean_object* v_a_308_, lean_object* v_b_309_){
_start:
{
lean_object* v_size_310_; lean_object* v_buckets_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_354_; 
v_size_310_ = lean_ctor_get(v_m_307_, 0);
v_buckets_311_ = lean_ctor_get(v_m_307_, 1);
v_isSharedCheck_354_ = !lean_is_exclusive(v_m_307_);
if (v_isSharedCheck_354_ == 0)
{
v___x_313_ = v_m_307_;
v_isShared_314_ = v_isSharedCheck_354_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_buckets_311_);
lean_inc(v_size_310_);
lean_dec(v_m_307_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_354_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; uint64_t v___x_316_; uint64_t v___x_317_; uint64_t v___x_318_; uint64_t v_fold_319_; uint64_t v___x_320_; uint64_t v___x_321_; uint64_t v___x_322_; size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; size_t v___x_326_; size_t v___x_327_; lean_object* v_bkt_328_; uint8_t v___x_329_; 
v___x_315_ = lean_array_get_size(v_buckets_311_);
v___x_316_ = l_Lean_instHashableFVarId_hash(v_a_308_);
v___x_317_ = 32ULL;
v___x_318_ = lean_uint64_shift_right(v___x_316_, v___x_317_);
v_fold_319_ = lean_uint64_xor(v___x_316_, v___x_318_);
v___x_320_ = 16ULL;
v___x_321_ = lean_uint64_shift_right(v_fold_319_, v___x_320_);
v___x_322_ = lean_uint64_xor(v_fold_319_, v___x_321_);
v___x_323_ = lean_uint64_to_usize(v___x_322_);
v___x_324_ = lean_usize_of_nat(v___x_315_);
v___x_325_ = ((size_t)1ULL);
v___x_326_ = lean_usize_sub(v___x_324_, v___x_325_);
v___x_327_ = lean_usize_land(v___x_323_, v___x_326_);
v_bkt_328_ = lean_array_uget_borrowed(v_buckets_311_, v___x_327_);
v___x_329_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_308_, v_bkt_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v_size_x27_331_; lean_object* v___x_332_; lean_object* v_buckets_x27_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_330_ = lean_unsigned_to_nat(1u);
v_size_x27_331_ = lean_nat_add(v_size_310_, v___x_330_);
lean_dec(v_size_310_);
lean_inc(v_bkt_328_);
v___x_332_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_332_, 0, v_a_308_);
lean_ctor_set(v___x_332_, 1, v_b_309_);
lean_ctor_set(v___x_332_, 2, v_bkt_328_);
v_buckets_x27_333_ = lean_array_uset(v_buckets_311_, v___x_327_, v___x_332_);
v___x_334_ = lean_unsigned_to_nat(4u);
v___x_335_ = lean_nat_mul(v_size_x27_331_, v___x_334_);
v___x_336_ = lean_unsigned_to_nat(3u);
v___x_337_ = lean_nat_div(v___x_335_, v___x_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_array_get_size(v_buckets_x27_333_);
v___x_339_ = lean_nat_dec_le(v___x_337_, v___x_338_);
lean_dec(v___x_337_);
if (v___x_339_ == 0)
{
lean_object* v_val_340_; lean_object* v___x_342_; 
v_val_340_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(v_buckets_x27_333_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 1, v_val_340_);
lean_ctor_set(v___x_313_, 0, v_size_x27_331_);
v___x_342_ = v___x_313_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_size_x27_331_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_val_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
else
{
lean_object* v___x_345_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 1, v_buckets_x27_333_);
lean_ctor_set(v___x_313_, 0, v_size_x27_331_);
v___x_345_ = v___x_313_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_size_x27_331_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_buckets_x27_333_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
else
{
lean_object* v___x_347_; lean_object* v_buckets_x27_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_352_; 
lean_inc(v_bkt_328_);
v___x_347_ = lean_box(0);
v_buckets_x27_348_ = lean_array_uset(v_buckets_311_, v___x_327_, v___x_347_);
v___x_349_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_308_, v_b_309_, v_bkt_328_);
v___x_350_ = lean_array_uset(v_buckets_x27_348_, v___x_327_, v___x_349_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 1, v___x_350_);
v___x_352_ = v___x_313_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_size_310_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(lean_object* v_p_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_fvarId_361_; lean_object* v_binderName_362_; lean_object* v_type_363_; uint8_t v_borrow_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_420_; 
v_fvarId_361_ = lean_ctor_get(v_p_355_, 0);
v_binderName_362_ = lean_ctor_get(v_p_355_, 1);
v_type_363_ = lean_ctor_get(v_p_355_, 2);
v_borrow_364_ = lean_ctor_get_uint8(v_p_355_, sizeof(void*)*3);
v_isSharedCheck_420_ = !lean_is_exclusive(v_p_355_);
if (v_isSharedCheck_420_ == 0)
{
v___x_366_ = v_p_355_;
v_isShared_367_ = v_isSharedCheck_420_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_type_363_);
lean_inc(v_binderName_362_);
lean_inc(v_fvarId_361_);
lean_dec(v_p_355_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_420_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_Compiler_LCNF_toImpureType(v_type_363_, v_a_358_, v_a_359_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_411_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_411_ == 0)
{
v___x_371_ = v___x_368_;
v_isShared_372_ = v_isSharedCheck_411_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_411_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___y_374_; uint8_t v___y_395_; uint8_t v___x_409_; 
v___x_409_ = l_Lean_Expr_isVoid(v_a_369_);
if (v___x_409_ == 0)
{
uint8_t v___x_410_; 
v___x_410_ = l_Lean_Expr_isErased(v_a_369_);
v___y_395_ = v___x_410_;
goto v___jp_394_;
}
else
{
v___y_395_ = v___x_409_;
goto v___jp_394_;
}
v___jp_373_:
{
lean_object* v___x_375_; lean_object* v_lctx_376_; lean_object* v_nextIdx_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_393_; 
v___x_375_ = lean_st_ref_take(v___y_374_);
v_lctx_376_ = lean_ctor_get(v___x_375_, 0);
v_nextIdx_377_ = lean_ctor_get(v___x_375_, 1);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_393_ == 0)
{
v___x_379_ = v___x_375_;
v_isShared_380_ = v_isSharedCheck_393_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_nextIdx_377_);
lean_inc(v_lctx_376_);
lean_dec(v___x_375_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_393_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
uint8_t v___x_381_; lean_object* v___x_383_; 
v___x_381_ = 1;
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 2, v_a_369_);
v___x_383_ = v___x_366_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_fvarId_361_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_binderName_362_);
lean_ctor_set(v_reuseFailAlloc_392_, 2, v_a_369_);
lean_ctor_set_uint8(v_reuseFailAlloc_392_, sizeof(void*)*3, v_borrow_364_);
v___x_383_ = v_reuseFailAlloc_392_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; lean_object* v___x_386_; 
lean_inc_ref(v___x_383_);
v___x_384_ = l_Lean_Compiler_LCNF_LCtx_addParam(v___x_381_, v_lctx_376_, v___x_383_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_384_);
v___x_386_ = v___x_379_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_384_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_nextIdx_377_);
v___x_386_ = v_reuseFailAlloc_391_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_387_ = lean_st_ref_put(v___y_374_, v___x_386_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_383_);
v___x_389_ = v___x_371_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_383_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
v___jp_394_:
{
if (v___y_395_ == 0)
{
v___y_374_ = v_a_357_;
goto v___jp_373_;
}
else
{
lean_object* v___x_396_; lean_object* v_subst_397_; lean_object* v_jpParamMask_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_408_; 
v___x_396_ = lean_st_ref_take(v_a_356_);
v_subst_397_ = lean_ctor_get(v___x_396_, 0);
v_jpParamMask_398_ = lean_ctor_get(v___x_396_, 1);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_408_ == 0)
{
v___x_400_ = v___x_396_;
v_isShared_401_ = v_isSharedCheck_408_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_jpParamMask_398_);
lean_inc(v_subst_397_);
lean_dec(v___x_396_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_408_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_402_ = lean_box(0);
lean_inc(v_fvarId_361_);
v___x_403_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_397_, v_fvarId_361_, v___x_402_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_403_);
v___x_405_ = v___x_400_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_jpParamMask_398_);
v___x_405_ = v_reuseFailAlloc_407_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; 
v___x_406_ = lean_st_ref_put(v_a_356_, v___x_405_);
v___y_374_ = v_a_357_;
goto v___jp_373_;
}
}
}
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_del_object(v___x_366_);
lean_dec(v_binderName_362_);
lean_dec(v_fvarId_361_);
v_a_412_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_368_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_368_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg___boxed(lean_object* v_p_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_p_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
lean_dec(v_a_423_);
lean_dec(v_a_422_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(lean_object* v_p_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_p_428_, v_a_429_, v_a_431_, v_a_432_, v_a_433_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___boxed(lean_object* v_p_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure(v_p_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec(v_a_437_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0(lean_object* v_00_u03b2_444_, lean_object* v_m_445_, lean_object* v_a_446_, lean_object* v_b_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_m_445_, v_a_446_, v_b_447_);
return v___x_448_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(lean_object* v_00_u03b2_449_, lean_object* v_a_450_, lean_object* v_x_451_){
_start:
{
uint8_t v___x_452_; 
v___x_452_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___redArg(v_a_450_, v_x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0___boxed(lean_object* v_00_u03b2_453_, lean_object* v_a_454_, lean_object* v_x_455_){
_start:
{
uint8_t v_res_456_; lean_object* v_r_457_; 
v_res_456_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__0(v_00_u03b2_453_, v_a_454_, v_x_455_);
lean_dec(v_x_455_);
lean_dec(v_a_454_);
v_r_457_ = lean_box(v_res_456_);
return v_r_457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1(lean_object* v_00_u03b2_458_, lean_object* v_data_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1___redArg(v_data_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2(lean_object* v_00_u03b2_461_, lean_object* v_a_462_, lean_object* v_b_463_, lean_object* v_x_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__2___redArg(v_a_462_, v_b_463_, v_x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_466_, lean_object* v_i_467_, lean_object* v_source_468_, lean_object* v_target_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2___redArg(v_i_467_, v_source_468_, v_target_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_471_, lean_object* v_x_472_, lean_object* v_x_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0_spec__1_spec__2_spec__3___redArg(v_x_472_, v_x_473_);
return v___x_474_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_box(0);
v___x_479_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1));
v___x_480_ = l_Lean_Expr_const___override(v___x_479_, v___x_478_);
return v___x_480_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__2);
v___x_482_ = lean_box(1);
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v___x_481_);
return v___x_483_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_box(0);
v___x_488_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__5));
v___x_489_ = l_Lean_Expr_const___override(v___x_488_, v___x_487_);
return v___x_489_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_493_ = lean_box(0);
v___x_494_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__8));
v___x_495_ = l_Lean_Expr_const___override(v___x_494_, v___x_493_);
return v___x_495_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_496_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__9);
v___x_497_ = lean_box(1);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v___x_496_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(lean_object* v_base_499_, lean_object* v_ctorInfo_500_, lean_object* v_field_501_){
_start:
{
switch(lean_obj_tag(v_field_501_))
{
case 0:
{
lean_object* v___x_502_; 
lean_dec(v_base_499_);
v___x_502_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__3);
return v___x_502_;
}
case 1:
{
lean_object* v_i_503_; lean_object* v_type_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_512_; 
v_i_503_ = lean_ctor_get(v_field_501_, 0);
v_type_504_ = lean_ctor_get(v_field_501_, 1);
v_isSharedCheck_512_ = !lean_is_exclusive(v_field_501_);
if (v_isSharedCheck_512_ == 0)
{
v___x_506_ = v_field_501_;
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_type_504_);
lean_inc(v_i_503_);
lean_dec(v_field_501_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set_tag(v___x_506_, 6);
lean_ctor_set(v___x_506_, 1, v_base_499_);
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_i_503_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_base_499_);
v___x_509_ = v_reuseFailAlloc_511_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_510_; 
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v_type_504_);
return v___x_510_;
}
}
}
case 2:
{
lean_object* v_i_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v_i_513_ = lean_ctor_get(v_field_501_, 0);
lean_inc(v_i_513_);
lean_dec_ref_known(v_field_501_, 1);
v___x_514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_514_, 0, v_i_513_);
lean_ctor_set(v___x_514_, 1, v_base_499_);
v___x_515_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
return v___x_516_;
}
case 3:
{
lean_object* v_offset_517_; lean_object* v_type_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_529_; 
v_offset_517_ = lean_ctor_get(v_field_501_, 1);
v_type_518_ = lean_ctor_get(v_field_501_, 2);
v_isSharedCheck_529_ = !lean_is_exclusive(v_field_501_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; 
v_unused_530_ = lean_ctor_get(v_field_501_, 0);
lean_dec(v_unused_530_);
v___x_520_ = v_field_501_;
v_isShared_521_ = v_isSharedCheck_529_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_type_518_);
lean_inc(v_offset_517_);
lean_dec(v_field_501_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_529_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v_size_522_; lean_object* v_usize_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v_size_522_ = lean_ctor_get(v_ctorInfo_500_, 2);
v_usize_523_ = lean_ctor_get(v_ctorInfo_500_, 3);
v___x_524_ = lean_nat_add(v_size_522_, v_usize_523_);
if (v_isShared_521_ == 0)
{
lean_ctor_set_tag(v___x_520_, 8);
lean_ctor_set(v___x_520_, 2, v_base_499_);
lean_ctor_set(v___x_520_, 0, v___x_524_);
v___x_526_ = v___x_520_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_offset_517_);
lean_ctor_set(v_reuseFailAlloc_528_, 2, v_base_499_);
v___x_526_ = v_reuseFailAlloc_528_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; 
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v_type_518_);
return v___x_527_;
}
}
}
default: 
{
lean_object* v___x_531_; 
lean_dec(v_base_499_);
v___x_531_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__10);
return v___x_531_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___boxed(lean_object* v_base_532_, lean_object* v_ctorInfo_533_, lean_object* v_field_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_base_532_, v_ctorInfo_533_, v_field_534_);
lean_dec_ref(v_ctorInfo_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(lean_object* v_arg_536_, lean_object* v_a_537_){
_start:
{
lean_object* v___x_539_; lean_object* v_subst_540_; uint8_t v___x_541_; uint8_t v___x_542_; lean_object* v___x_543_; 
v___x_539_ = lean_st_ref_get(v_a_537_);
v_subst_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc_ref(v_subst_540_);
lean_dec(v___x_539_);
v___x_541_ = 0;
v___x_542_ = 1;
v___x_543_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(v___x_541_, v_subst_540_, v_arg_536_, v___x_542_);
lean_dec_ref(v_subst_540_);
if (lean_obj_tag(v___x_543_) == 1)
{
lean_object* v_fvarId_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_552_; 
v_fvarId_544_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_552_ == 0)
{
v___x_546_ = v___x_543_;
v_isShared_547_ = v_isSharedCheck_552_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_fvarId_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_552_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_fvarId_544_);
v___x_549_ = v_reuseFailAlloc_551_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; 
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
}
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec(v___x_543_);
v___x_553_ = lean_box(0);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg___boxed(lean_object* v_arg_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_arg_555_, v_a_556_);
lean_dec(v_a_556_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(lean_object* v_arg_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_arg_559_, v_a_560_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___boxed(lean_object* v_arg_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure(v_arg_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity_spec__0(lean_object* v_msg_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = l_Lean_instInhabitedExpr;
v___x_577_ = lean_panic_fn_borrowed(v___x_576_, v_msg_575_);
return v___x_577_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_581_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__2));
v___x_582_ = lean_unsigned_to_nat(11u);
v___x_583_ = lean_unsigned_to_nat(83u);
v___x_584_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__1));
v___x_585_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_586_ = l_mkPanicMessageWithDecl(v___x_585_, v___x_584_, v___x_583_, v___x_582_, v___x_581_);
return v___x_586_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_587_ = lean_box(0);
v___x_588_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__1));
v___x_589_ = l_Lean_mkConst(v___x_588_, v___x_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(lean_object* v_type_590_, lean_object* v_arity_591_){
_start:
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = lean_nat_dec_eq(v_arity_591_, v___x_595_);
if (v___x_596_ == 0)
{
switch(lean_obj_tag(v_type_590_))
{
case 7:
{
lean_object* v_body_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_body_597_ = lean_ctor_get(v_type_590_, 2);
v___x_598_ = lean_unsigned_to_nat(1u);
v___x_599_ = lean_nat_sub(v_arity_591_, v___x_598_);
lean_dec(v_arity_591_);
v_type_590_ = v_body_597_;
v_arity_591_ = v___x_599_;
goto _start;
}
case 4:
{
lean_object* v_declName_601_; 
lean_dec(v_arity_591_);
v_declName_601_ = lean_ctor_get(v_type_590_, 0);
if (lean_obj_tag(v_declName_601_) == 1)
{
lean_object* v_pre_602_; 
v_pre_602_ = lean_ctor_get(v_declName_601_, 0);
if (lean_obj_tag(v_pre_602_) == 0)
{
lean_object* v_str_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v_str_603_ = lean_ctor_get(v_declName_601_, 1);
v___x_604_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__0));
v___x_605_ = lean_string_dec_eq(v_str_603_, v___x_604_);
if (v___x_605_ == 0)
{
goto v___jp_592_;
}
else
{
lean_object* v___x_606_; 
v___x_606_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__4);
return v___x_606_;
}
}
else
{
goto v___jp_592_;
}
}
else
{
goto v___jp_592_;
}
}
default: 
{
lean_dec(v_arity_591_);
goto v___jp_592_;
}
}
}
else
{
lean_dec(v_arity_591_);
lean_inc_ref(v_type_590_);
return v_type_590_;
}
v___jp_592_:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__3);
v___x_594_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity_spec__0(v___x_593_);
return v___x_594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___boxed(lean_object* v_type_607_, lean_object* v_arity_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(v_type_607_, v_arity_608_);
lean_dec_ref(v_type_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lowerResultType(lean_object* v_type_610_, lean_object* v_arity_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity(v_type_610_, v_arity_611_);
v___x_616_ = l_Lean_Compiler_LCNF_toImpureType(v___x_615_, v_a_612_, v_a_613_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_lowerResultType___boxed(lean_object* v_type_617_, lean_object* v_arity_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_617_, v_arity_618_, v_a_619_, v_a_620_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
lean_dec_ref(v_type_617_);
return v_res_622_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_box(0);
v___x_627_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__1));
v___x_628_ = l_Lean_Expr_const___override(v___x_627_, v___x_626_);
return v___x_628_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = lean_box(0);
v___x_633_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__4));
v___x_634_ = l_Lean_Expr_const___override(v___x_633_, v___x_632_);
return v___x_634_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = lean_box(0);
v___x_639_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__7));
v___x_640_ = l_Lean_Expr_const___override(v___x_639_, v___x_638_);
return v___x_640_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = lean_box(0);
v___x_645_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__10));
v___x_646_ = l_Lean_Expr_const___override(v___x_645_, v___x_644_);
return v___x_646_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = lean_box(0);
v___x_651_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__13));
v___x_652_ = l_Lean_Expr_const___override(v___x_651_, v___x_650_);
return v___x_652_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = lean_box(0);
v___x_657_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__16));
v___x_658_ = l_Lean_Expr_const___override(v___x_657_, v___x_656_);
return v___x_658_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_662_ = lean_box(0);
v___x_663_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__19));
v___x_664_ = l_Lean_Expr_const___override(v___x_663_, v___x_662_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(lean_object* v_v_665_){
_start:
{
switch(lean_obj_tag(v_v_665_))
{
case 0:
{
lean_object* v_val_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v_val_666_ = lean_ctor_get(v_v_665_, 0);
v___x_667_ = lean_cstr_to_nat("4294967296");
v___x_668_ = lean_nat_dec_lt(v_val_666_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
v___x_669_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2);
return v___x_669_;
}
else
{
lean_object* v___x_670_; 
v___x_670_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5);
return v___x_670_;
}
}
case 1:
{
lean_object* v___x_671_; 
v___x_671_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
return v___x_671_;
}
case 2:
{
lean_object* v___x_672_; 
v___x_672_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__11);
return v___x_672_;
}
case 3:
{
lean_object* v___x_673_; 
v___x_673_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__14);
return v___x_673_;
}
case 4:
{
lean_object* v___x_674_; 
v___x_674_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__17);
return v___x_674_;
}
case 5:
{
lean_object* v___x_675_; 
v___x_675_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__20);
return v___x_675_;
}
default: 
{
lean_object* v___x_676_; 
v___x_676_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj___closed__6);
return v___x_676_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___boxed(lean_object* v_v_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(v_v_677_);
lean_dec_ref(v_v_677_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(lean_object* v_as_679_, size_t v_i_680_, size_t v_stop_681_, lean_object* v_b_682_){
_start:
{
lean_object* v___y_684_; uint8_t v___x_688_; 
v___x_688_ = lean_usize_dec_eq(v_i_680_, v_stop_681_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v_snd_690_; uint8_t v___x_691_; 
v___x_689_ = lean_array_uget_borrowed(v_as_679_, v_i_680_);
v_snd_690_ = lean_ctor_get(v___x_689_, 1);
v___x_691_ = lean_unbox(v_snd_690_);
if (v___x_691_ == 0)
{
v___y_684_ = v_b_682_;
goto v___jp_683_;
}
else
{
lean_object* v_fst_692_; lean_object* v___x_693_; 
v_fst_692_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_fst_692_);
v___x_693_ = lean_array_push(v_b_682_, v_fst_692_);
v___y_684_ = v___x_693_;
goto v___jp_683_;
}
}
else
{
return v_b_682_;
}
v___jp_683_:
{
size_t v___x_685_; size_t v___x_686_; 
v___x_685_ = ((size_t)1ULL);
v___x_686_ = lean_usize_add(v_i_680_, v___x_685_);
v_i_680_ = v___x_686_;
v_b_682_ = v___y_684_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4___boxed(lean_object* v_as_694_, lean_object* v_i_695_, lean_object* v_stop_696_, lean_object* v_b_697_){
_start:
{
size_t v_i_boxed_698_; size_t v_stop_boxed_699_; lean_object* v_res_700_; 
v_i_boxed_698_ = lean_unbox_usize(v_i_695_);
lean_dec(v_i_695_);
v_stop_boxed_699_ = lean_unbox_usize(v_stop_696_);
lean_dec(v_stop_696_);
v_res_700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v_as_694_, v_i_boxed_698_, v_stop_boxed_699_, v_b_697_);
lean_dec_ref(v_as_694_);
return v_res_700_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0(void){
_start:
{
uint8_t v___x_701_; lean_object* v___x_702_; 
v___x_701_ = 1;
v___x_702_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(lean_object* v_msg_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_710_; lean_object* v_toApplicative_711_; lean_object* v_toFunctor_712_; lean_object* v_toSeq_713_; lean_object* v_toSeqLeft_714_; lean_object* v_toSeqRight_715_; lean_object* v___f_716_; lean_object* v___f_717_; lean_object* v___f_718_; lean_object* v___f_719_; lean_object* v___x_720_; lean_object* v___f_721_; lean_object* v___f_722_; lean_object* v___f_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v_toApplicative_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_759_; 
v___x_710_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__1);
v_toApplicative_711_ = lean_ctor_get(v___x_710_, 0);
v_toFunctor_712_ = lean_ctor_get(v_toApplicative_711_, 0);
v_toSeq_713_ = lean_ctor_get(v_toApplicative_711_, 2);
v_toSeqLeft_714_ = lean_ctor_get(v_toApplicative_711_, 3);
v_toSeqRight_715_ = lean_ctor_get(v_toApplicative_711_, 4);
v___f_716_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__2));
v___f_717_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__3));
lean_inc_ref_n(v_toFunctor_712_, 2);
v___f_718_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_718_, 0, v_toFunctor_712_);
v___f_719_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_719_, 0, v_toFunctor_712_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v___f_718_);
lean_ctor_set(v___x_720_, 1, v___f_719_);
lean_inc(v_toSeqRight_715_);
v___f_721_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_721_, 0, v_toSeqRight_715_);
lean_inc(v_toSeqLeft_714_);
v___f_722_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_722_, 0, v_toSeqLeft_714_);
lean_inc(v_toSeq_713_);
v___f_723_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_723_, 0, v_toSeq_713_);
v___x_724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_724_, 0, v___x_720_);
lean_ctor_set(v___x_724_, 1, v___f_716_);
lean_ctor_set(v___x_724_, 2, v___f_723_);
lean_ctor_set(v___x_724_, 3, v___f_722_);
lean_ctor_set(v___x_724_, 4, v___f_721_);
v___x_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v___f_717_);
v___x_726_ = l_StateRefT_x27_instMonad___redArg(v___x_725_);
v_toApplicative_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; 
v_unused_760_ = lean_ctor_get(v___x_726_, 1);
lean_dec(v_unused_760_);
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_759_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_toApplicative_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_759_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v_toFunctor_731_; lean_object* v_toSeq_732_; lean_object* v_toSeqLeft_733_; lean_object* v_toSeqRight_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_757_; 
v_toFunctor_731_ = lean_ctor_get(v_toApplicative_727_, 0);
v_toSeq_732_ = lean_ctor_get(v_toApplicative_727_, 2);
v_toSeqLeft_733_ = lean_ctor_get(v_toApplicative_727_, 3);
v_toSeqRight_734_ = lean_ctor_get(v_toApplicative_727_, 4);
v_isSharedCheck_757_ = !lean_is_exclusive(v_toApplicative_727_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; 
v_unused_758_ = lean_ctor_get(v_toApplicative_727_, 1);
lean_dec(v_unused_758_);
v___x_736_ = v_toApplicative_727_;
v_isShared_737_ = v_isSharedCheck_757_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_toSeqRight_734_);
lean_inc(v_toSeqLeft_733_);
lean_inc(v_toSeq_732_);
lean_inc(v_toFunctor_731_);
lean_dec(v_toApplicative_727_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_757_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___f_738_; lean_object* v___f_739_; lean_object* v___f_740_; lean_object* v___f_741_; lean_object* v___x_742_; lean_object* v___f_743_; lean_object* v___f_744_; lean_object* v___f_745_; lean_object* v___x_747_; 
v___f_738_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__5));
v___f_739_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_instMonadFVarSubstToImpureMPureTrue___closed__6));
lean_inc_ref(v_toFunctor_731_);
v___f_740_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_740_, 0, v_toFunctor_731_);
v___f_741_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_741_, 0, v_toFunctor_731_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v___f_740_);
lean_ctor_set(v___x_742_, 1, v___f_741_);
v___f_743_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_743_, 0, v_toSeqRight_734_);
v___f_744_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_744_, 0, v_toSeqLeft_733_);
v___f_745_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_745_, 0, v_toSeq_732_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 4, v___f_743_);
lean_ctor_set(v___x_736_, 3, v___f_744_);
lean_ctor_set(v___x_736_, 2, v___f_745_);
lean_ctor_set(v___x_736_, 1, v___f_738_);
lean_ctor_set(v___x_736_, 0, v___x_742_);
v___x_747_ = v___x_736_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v___f_738_);
lean_ctor_set(v_reuseFailAlloc_756_, 2, v___f_745_);
lean_ctor_set(v_reuseFailAlloc_756_, 3, v___f_744_);
lean_ctor_set(v_reuseFailAlloc_756_, 4, v___f_743_);
v___x_747_ = v_reuseFailAlloc_756_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_749_; 
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v___f_739_);
lean_ctor_set(v___x_729_, 0, v___x_747_);
v___x_749_ = v___x_729_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v___f_739_);
v___x_749_ = v_reuseFailAlloc_755_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_35569__overap_753_; lean_object* v___x_754_; 
v___x_750_ = l_StateRefT_x27_instMonad___redArg(v___x_749_);
v___x_751_ = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___closed__0);
v___x_752_ = l_instInhabitedOfMonad___redArg(v___x_750_, v___x_751_);
v___x_35569__overap_753_ = lean_panic_fn_borrowed(v___x_752_, v_msg_703_);
lean_dec(v___x_752_);
lean_inc(v___y_708_);
lean_inc_ref(v___y_707_);
lean_inc(v___y_706_);
lean_inc_ref(v___y_705_);
lean_inc(v___y_704_);
v___x_754_ = lean_apply_6(v___x_35569__overap_753_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, lean_box(0));
return v___x_754_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0___boxed(lean_object* v_msg_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v_msg_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
return v_res_768_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0(void){
_start:
{
uint8_t v___x_769_; lean_object* v___x_770_; 
v___x_769_ = 0;
v___x_770_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(lean_object* v_upperBound_771_, lean_object* v_params_772_, lean_object* v___x_773_, lean_object* v_discr_774_, lean_object* v_a_775_, lean_object* v_b_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_a_780_; uint8_t v___x_784_; 
v___x_784_ = lean_nat_dec_lt(v_a_775_, v_upperBound_771_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
lean_dec(v_a_775_);
lean_dec(v_discr_774_);
v___x_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_785_, 0, v_b_776_);
return v___x_785_;
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_786_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___closed__0);
v___x_787_ = lean_box(0);
v___x_788_ = lean_array_get_borrowed(v___x_786_, v_params_772_, v_a_775_);
v___x_789_ = lean_nat_dec_eq(v_a_775_, v___x_773_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v_fvarId_791_; lean_object* v_subst_792_; lean_object* v_jpParamMask_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_803_; 
v___x_790_ = lean_st_ref_take(v___y_777_);
v_fvarId_791_ = lean_ctor_get(v___x_788_, 0);
v_subst_792_ = lean_ctor_get(v___x_790_, 0);
v_jpParamMask_793_ = lean_ctor_get(v___x_790_, 1);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_803_ == 0)
{
v___x_795_ = v___x_790_;
v_isShared_796_ = v_isSharedCheck_803_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_jpParamMask_793_);
lean_inc(v_subst_792_);
lean_dec(v___x_790_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_803_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_797_ = lean_box(0);
lean_inc(v_fvarId_791_);
v___x_798_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_792_, v_fvarId_791_, v___x_797_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_798_);
v___x_800_ = v___x_795_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_jpParamMask_793_);
v___x_800_ = v_reuseFailAlloc_802_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; 
v___x_801_ = lean_st_ref_put(v___y_777_, v___x_800_);
v_a_780_ = v___x_787_;
goto v___jp_779_;
}
}
}
else
{
lean_object* v___x_804_; lean_object* v_fvarId_805_; lean_object* v_subst_806_; lean_object* v_jpParamMask_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_817_; 
v___x_804_ = lean_st_ref_take(v___y_777_);
v_fvarId_805_ = lean_ctor_get(v___x_788_, 0);
v_subst_806_ = lean_ctor_get(v___x_804_, 0);
v_jpParamMask_807_ = lean_ctor_get(v___x_804_, 1);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_817_ == 0)
{
v___x_809_ = v___x_804_;
v_isShared_810_ = v_isSharedCheck_817_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_jpParamMask_807_);
lean_inc(v_subst_806_);
lean_dec(v___x_804_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_817_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_814_; 
lean_inc(v_discr_774_);
v___x_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_811_, 0, v_discr_774_);
lean_inc(v_fvarId_805_);
v___x_812_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_806_, v_fvarId_805_, v___x_811_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_812_);
v___x_814_ = v___x_809_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_jpParamMask_807_);
v___x_814_ = v_reuseFailAlloc_816_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; 
v___x_815_ = lean_st_ref_put(v___y_777_, v___x_814_);
v_a_780_ = v___x_787_;
goto v___jp_779_;
}
}
}
}
v___jp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_unsigned_to_nat(1u);
v___x_782_ = lean_nat_add(v_a_775_, v___x_781_);
lean_dec(v_a_775_);
v_a_775_ = v___x_782_;
v_b_776_ = v_a_780_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg___boxed(lean_object* v_upperBound_818_, lean_object* v_params_819_, lean_object* v___x_820_, lean_object* v_discr_821_, lean_object* v_a_822_, lean_object* v_b_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v_upperBound_818_, v_params_819_, v___x_820_, v_discr_821_, v_a_822_, v_b_823_, v___y_824_);
lean_dec(v___y_824_);
lean_dec(v___x_820_);
lean_dec_ref(v_params_819_);
lean_dec(v_upperBound_818_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(size_t v_sz_827_, size_t v_i_828_, lean_object* v_bs_829_){
_start:
{
uint8_t v___x_830_; 
v___x_830_ = lean_usize_dec_lt(v_i_828_, v_sz_827_);
if (v___x_830_ == 0)
{
return v_bs_829_;
}
else
{
lean_object* v_v_831_; lean_object* v_type_832_; lean_object* v___x_833_; lean_object* v_bs_x27_834_; uint8_t v___y_836_; uint8_t v___y_843_; uint8_t v___x_845_; 
v_v_831_ = lean_array_uget_borrowed(v_bs_829_, v_i_828_);
v_type_832_ = lean_ctor_get(v_v_831_, 2);
lean_inc_ref(v_type_832_);
v___x_833_ = lean_unsigned_to_nat(0u);
v_bs_x27_834_ = lean_array_uset(v_bs_829_, v_i_828_, v___x_833_);
v___x_845_ = l_Lean_Expr_isVoid(v_type_832_);
if (v___x_845_ == 0)
{
uint8_t v___x_846_; 
v___x_846_ = l_Lean_Expr_isErased(v_type_832_);
lean_dec_ref(v_type_832_);
v___y_843_ = v___x_846_;
goto v___jp_842_;
}
else
{
lean_dec_ref(v_type_832_);
v___y_843_ = v___x_845_;
goto v___jp_842_;
}
v___jp_835_:
{
size_t v___x_837_; size_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_837_ = ((size_t)1ULL);
v___x_838_ = lean_usize_add(v_i_828_, v___x_837_);
v___x_839_ = lean_box(v___y_836_);
v___x_840_ = lean_array_uset(v_bs_x27_834_, v_i_828_, v___x_839_);
v_i_828_ = v___x_838_;
v_bs_829_ = v___x_840_;
goto _start;
}
v___jp_842_:
{
if (v___y_843_ == 0)
{
v___y_836_ = v___x_830_;
goto v___jp_835_;
}
else
{
uint8_t v___x_844_; 
v___x_844_ = 0;
v___y_836_ = v___x_844_;
goto v___jp_835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3___boxed(lean_object* v_sz_847_, lean_object* v_i_848_, lean_object* v_bs_849_){
_start:
{
size_t v_sz_boxed_850_; size_t v_i_boxed_851_; lean_object* v_res_852_; 
v_sz_boxed_850_ = lean_unbox_usize(v_sz_847_);
lean_dec(v_sz_847_);
v_i_boxed_851_ = lean_unbox_usize(v_i_848_);
lean_dec(v_i_848_);
v_res_852_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(v_sz_boxed_850_, v_i_boxed_851_, v_bs_849_);
return v_res_852_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_853_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__0);
v___x_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_856_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__1);
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
lean_ctor_set(v___x_858_, 2, v___x_857_);
lean_ctor_set(v___x_858_, 3, v___x_857_);
lean_ctor_set(v___x_858_, 4, v___x_856_);
lean_ctor_set(v___x_858_, 5, v___x_856_);
lean_ctor_set(v___x_858_, 6, v___x_856_);
lean_ctor_set(v___x_858_, 7, v___x_856_);
lean_ctor_set(v___x_858_, 8, v___x_856_);
lean_ctor_set(v___x_858_, 9, v___x_856_);
lean_ctor_set(v___x_858_, 10, v___x_856_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(lean_object* v_msg_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v_toCold_865_; lean_object* v_ref_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_toCold_865_ = lean_ctor_get(v___y_862_, 0);
v_ref_866_ = lean_ctor_get(v___y_862_, 2);
v___x_867_ = lean_st_ref_get(v___y_863_);
v___x_868_ = lean_st_ref_get(v___y_861_);
v___x_869_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_860_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_893_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_893_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_893_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_893_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v_env_874_; lean_object* v_lctx_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_891_; 
v_env_874_ = lean_ctor_get(v___x_867_, 0);
lean_inc_ref(v_env_874_);
lean_dec(v___x_867_);
v_lctx_875_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_891_ == 0)
{
lean_object* v_unused_892_; 
v_unused_892_ = lean_ctor_get(v___x_868_, 1);
lean_dec(v_unused_892_);
v___x_877_ = v___x_868_;
v_isShared_878_ = v_isSharedCheck_891_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_lctx_875_);
lean_dec(v___x_868_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_891_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v_options_879_; uint8_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
v_options_879_ = lean_ctor_get(v_toCold_865_, 2);
v___x_880_ = lean_unbox(v_a_870_);
lean_dec(v_a_870_);
v___x_881_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_875_, v___x_880_);
lean_dec_ref(v_lctx_875_);
v___x_882_ = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___closed__2);
lean_inc_ref(v_options_879_);
v___x_883_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_883_, 0, v_env_874_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
lean_ctor_set(v___x_883_, 2, v___x_881_);
lean_ctor_set(v___x_883_, 3, v_options_879_);
if (v_isShared_878_ == 0)
{
lean_ctor_set_tag(v___x_877_, 3);
lean_ctor_set(v___x_877_, 1, v_msg_859_);
lean_ctor_set(v___x_877_, 0, v___x_883_);
v___x_885_ = v___x_877_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_msg_859_);
v___x_885_ = v_reuseFailAlloc_890_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_886_; lean_object* v___x_888_; 
lean_inc(v_ref_866_);
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v_ref_866_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
if (v_isShared_873_ == 0)
{
lean_ctor_set_tag(v___x_872_, 1);
lean_ctor_set(v___x_872_, 0, v___x_886_);
v___x_888_ = v___x_872_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec(v___x_868_);
lean_dec(v___x_867_);
lean_dec_ref(v_msg_859_);
v_a_894_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_869_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_869_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg___boxed(lean_object* v_msg_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_msg_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(size_t v_sz_909_, size_t v_i_910_, lean_object* v_bs_911_, lean_object* v___y_912_){
_start:
{
uint8_t v___x_914_; 
v___x_914_ = lean_usize_dec_lt(v_i_910_, v_sz_909_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; 
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v_bs_911_);
return v___x_915_;
}
else
{
lean_object* v_v_916_; lean_object* v___x_917_; 
v_v_916_ = lean_array_uget_borrowed(v_bs_911_, v_i_910_);
lean_inc(v_v_916_);
v___x_917_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_v_916_, v___y_912_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_919_; lean_object* v_bs_x27_920_; size_t v___x_921_; size_t v___x_922_; lean_object* v___x_923_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
lean_dec_ref_known(v___x_917_, 1);
v___x_919_ = lean_unsigned_to_nat(0u);
v_bs_x27_920_ = lean_array_uset(v_bs_911_, v_i_910_, v___x_919_);
v___x_921_ = ((size_t)1ULL);
v___x_922_ = lean_usize_add(v_i_910_, v___x_921_);
v___x_923_ = lean_array_uset(v_bs_x27_920_, v_i_910_, v_a_918_);
v_i_910_ = v___x_922_;
v_bs_911_ = v___x_923_;
goto _start;
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v_bs_911_);
v_a_925_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_917_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_917_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg___boxed(lean_object* v_sz_933_, lean_object* v_i_934_, lean_object* v_bs_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
size_t v_sz_boxed_938_; size_t v_i_boxed_939_; lean_object* v_res_940_; 
v_sz_boxed_938_ = lean_unbox_usize(v_sz_933_);
lean_dec(v_sz_933_);
v_i_boxed_939_ = lean_unbox_usize(v_i_934_);
lean_dec(v_i_934_);
v_res_940_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_boxed_938_, v_i_boxed_939_, v_bs_935_, v___y_936_);
lean_dec(v___y_936_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(lean_object* v_upperBound_941_, lean_object* v_fieldInfo_942_, lean_object* v___x_943_, lean_object* v_a_944_, lean_object* v_b_945_){
_start:
{
lean_object* v_a_948_; uint8_t v___x_952_; 
v___x_952_ = lean_nat_dec_lt(v_a_944_, v_upperBound_941_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
lean_dec(v_a_944_);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v_b_945_);
return v___x_953_;
}
else
{
lean_object* v___x_954_; 
v___x_954_ = lean_array_fget_borrowed(v_fieldInfo_942_, v_a_944_);
switch(lean_obj_tag(v___x_954_))
{
case 1:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_955_ = lean_box(0);
v___x_956_ = lean_array_get_borrowed(v___x_955_, v___x_943_, v_a_944_);
lean_inc(v___x_956_);
v___x_957_ = lean_array_push(v_b_945_, v___x_956_);
v_a_948_ = v___x_957_;
goto v___jp_947_;
}
case 2:
{
v_a_948_ = v_b_945_;
goto v___jp_947_;
}
case 3:
{
v_a_948_ = v_b_945_;
goto v___jp_947_;
}
default: 
{
v_a_948_ = v_b_945_;
goto v___jp_947_;
}
}
}
v___jp_947_:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = lean_unsigned_to_nat(1u);
v___x_950_ = lean_nat_add(v_a_944_, v___x_949_);
lean_dec(v_a_944_);
v_a_944_ = v___x_950_;
v_b_945_ = v_a_948_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg___boxed(lean_object* v_upperBound_958_, lean_object* v_fieldInfo_959_, lean_object* v___x_960_, lean_object* v_a_961_, lean_object* v_b_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v_upperBound_958_, v_fieldInfo_959_, v___x_960_, v_a_961_, v_b_962_);
lean_dec_ref(v___x_960_);
lean_dec_ref(v_fieldInfo_959_);
lean_dec(v_upperBound_958_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(lean_object* v_as_965_, size_t v_i_966_, size_t v_stop_967_, lean_object* v_b_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_a_972_; uint8_t v___x_976_; 
v___x_976_ = lean_usize_dec_eq(v_i_966_, v_stop_967_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; lean_object* v_snd_978_; uint8_t v___x_979_; 
v___x_977_ = lean_array_uget_borrowed(v_as_965_, v_i_966_);
v_snd_978_ = lean_ctor_get(v___x_977_, 1);
v___x_979_ = lean_unbox(v_snd_978_);
if (v___x_979_ == 0)
{
v_a_972_ = v_b_968_;
goto v___jp_971_;
}
else
{
lean_object* v_fst_980_; lean_object* v___x_981_; 
v_fst_980_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_fst_980_);
v___x_981_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Arg_toImpure___redArg(v_fst_980_, v___y_969_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v___x_983_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_981_, 1);
v___x_983_ = lean_array_push(v_b_968_, v_a_982_);
v_a_972_ = v___x_983_;
goto v___jp_971_;
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec_ref(v_b_968_);
v_a_984_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_981_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_981_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
else
{
lean_object* v___x_992_; 
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v_b_968_);
return v___x_992_;
}
v___jp_971_:
{
size_t v___x_973_; size_t v___x_974_; 
v___x_973_ = ((size_t)1ULL);
v___x_974_ = lean_usize_add(v_i_966_, v___x_973_);
v_i_966_ = v___x_974_;
v_b_968_ = v_a_972_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg___boxed(lean_object* v_as_993_, lean_object* v_i_994_, lean_object* v_stop_995_, lean_object* v_b_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
size_t v_i_boxed_999_; size_t v_stop_boxed_1000_; lean_object* v_res_1001_; 
v_i_boxed_999_ = lean_unbox_usize(v_i_994_);
lean_dec(v_i_994_);
v_stop_boxed_1000_ = lean_unbox_usize(v_stop_995_);
lean_dec(v_stop_995_);
v_res_1001_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v_as_993_, v_i_boxed_999_, v_stop_boxed_1000_, v_b_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v_as_993_);
return v_res_1001_;
}
}
static lean_object* _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0(void){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Array_instInhabited(lean_box(0));
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17(lean_object* v_msg_1003_){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = lean_obj_once(&l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0, &l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0_once, _init_l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17___closed__0);
v___x_1005_ = lean_panic_fn_borrowed(v___x_1004_, v_msg_1003_);
return v___x_1005_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1009_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__2));
v___x_1010_ = lean_unsigned_to_nat(11u);
v___x_1011_ = lean_unsigned_to_nat(163u);
v___x_1012_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__1));
v___x_1013_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__0));
v___x_1014_ = l_mkPanicMessageWithDecl(v___x_1013_, v___x_1012_, v___x_1011_, v___x_1010_, v___x_1009_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(lean_object* v_a_1015_, lean_object* v_x_1016_){
_start:
{
if (lean_obj_tag(v_x_1016_) == 0)
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___closed__3);
v___x_1018_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13_spec__17(v___x_1017_);
return v___x_1018_;
}
else
{
lean_object* v_key_1019_; lean_object* v_value_1020_; lean_object* v_tail_1021_; uint8_t v___x_1022_; 
v_key_1019_ = lean_ctor_get(v_x_1016_, 0);
v_value_1020_ = lean_ctor_get(v_x_1016_, 1);
v_tail_1021_ = lean_ctor_get(v_x_1016_, 2);
v___x_1022_ = l_Lean_instBEqFVarId_beq(v_key_1019_, v_a_1015_);
if (v___x_1022_ == 0)
{
v_x_1016_ = v_tail_1021_;
goto _start;
}
else
{
lean_inc(v_value_1020_);
return v_value_1020_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13___boxed(lean_object* v_a_1024_, lean_object* v_x_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(v_a_1024_, v_x_1025_);
lean_dec(v_x_1025_);
lean_dec(v_a_1024_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(lean_object* v_m_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v_buckets_1029_; lean_object* v___x_1030_; uint64_t v___x_1031_; uint64_t v___x_1032_; uint64_t v___x_1033_; uint64_t v_fold_1034_; uint64_t v___x_1035_; uint64_t v___x_1036_; uint64_t v___x_1037_; size_t v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; size_t v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v_buckets_1029_ = lean_ctor_get(v_m_1027_, 1);
v___x_1030_ = lean_array_get_size(v_buckets_1029_);
v___x_1031_ = l_Lean_instHashableFVarId_hash(v_a_1028_);
v___x_1032_ = 32ULL;
v___x_1033_ = lean_uint64_shift_right(v___x_1031_, v___x_1032_);
v_fold_1034_ = lean_uint64_xor(v___x_1031_, v___x_1033_);
v___x_1035_ = 16ULL;
v___x_1036_ = lean_uint64_shift_right(v_fold_1034_, v___x_1035_);
v___x_1037_ = lean_uint64_xor(v_fold_1034_, v___x_1036_);
v___x_1038_ = lean_uint64_to_usize(v___x_1037_);
v___x_1039_ = lean_usize_of_nat(v___x_1030_);
v___x_1040_ = ((size_t)1ULL);
v___x_1041_ = lean_usize_sub(v___x_1039_, v___x_1040_);
v___x_1042_ = lean_usize_land(v___x_1038_, v___x_1041_);
v___x_1043_ = lean_array_uget_borrowed(v_buckets_1029_, v___x_1042_);
v___x_1044_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5_spec__13(v_a_1028_, v___x_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5___boxed(lean_object* v_m_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(v_m_1045_, v_a_1046_);
lean_dec(v_a_1046_);
lean_dec_ref(v_m_1045_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(size_t v_sz_1048_, size_t v_i_1049_, lean_object* v_bs_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
uint8_t v___x_1056_; 
v___x_1056_ = lean_usize_dec_lt(v_i_1049_, v_sz_1048_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; 
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v_bs_1050_);
return v___x_1057_;
}
else
{
lean_object* v_v_1058_; lean_object* v___x_1059_; 
v_v_1058_ = lean_array_uget_borrowed(v_bs_1050_, v_i_1049_);
lean_inc(v_v_1058_);
v___x_1059_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure___redArg(v_v_1058_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1061_; lean_object* v_bs_x27_1062_; size_t v___x_1063_; size_t v___x_1064_; lean_object* v___x_1065_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v___x_1061_ = lean_unsigned_to_nat(0u);
v_bs_x27_1062_ = lean_array_uset(v_bs_1050_, v_i_1049_, v___x_1061_);
v___x_1063_ = ((size_t)1ULL);
v___x_1064_ = lean_usize_add(v_i_1049_, v___x_1063_);
v___x_1065_ = lean_array_uset(v_bs_x27_1062_, v_i_1049_, v_a_1060_);
v_i_1049_ = v___x_1064_;
v_bs_1050_ = v___x_1065_;
goto _start;
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_dec_ref(v_bs_1050_);
v_a_1067_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1059_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1059_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg___boxed(lean_object* v_sz_1075_, lean_object* v_i_1076_, lean_object* v_bs_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
size_t v_sz_boxed_1083_; size_t v_i_boxed_1084_; lean_object* v_res_1085_; 
v_sz_boxed_1083_ = lean_unbox_usize(v_sz_1075_);
lean_dec(v_sz_1075_);
v_i_boxed_1084_ = lean_unbox_usize(v_i_1076_);
lean_dec(v_i_1076_);
v_res_1085_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_boxed_1083_, v_i_boxed_1084_, v_bs_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec(v___y_1078_);
return v_res_1085_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1088_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__1));
v___x_1089_ = lean_unsigned_to_nat(12u);
v___x_1090_ = lean_unsigned_to_nat(116u);
v___x_1091_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0));
v___x_1092_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1093_ = l_mkPanicMessageWithDecl(v___x_1092_, v___x_1091_, v___x_1090_, v___x_1089_, v___x_1088_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(lean_object* v_k_1094_, lean_object* v_decl_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v___x_1102_; lean_object* v_lctx_1103_; lean_object* v_nextIdx_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1124_; 
v___x_1102_ = lean_st_ref_take(v_a_1098_);
v_lctx_1103_ = lean_ctor_get(v___x_1102_, 0);
v_nextIdx_1104_ = lean_ctor_get(v___x_1102_, 1);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1106_ = v___x_1102_;
v_isShared_1107_ = v_isSharedCheck_1124_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_nextIdx_1104_);
lean_inc(v_lctx_1103_);
lean_dec(v___x_1102_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1124_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
uint8_t v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1108_ = 1;
lean_inc_ref(v_decl_1095_);
v___x_1109_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1108_, v_lctx_1103_, v_decl_1095_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 0, v___x_1109_);
v___x_1111_ = v___x_1106_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_nextIdx_1104_);
v___x_1111_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = lean_st_ref_put(v_a_1098_, v___x_1111_);
v___x_1113_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1094_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1122_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1116_ = v___x_1113_;
v_isShared_1117_ = v_isSharedCheck_1122_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1122_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v___x_1120_; 
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v_decl_1095_);
lean_ctor_set(v___x_1118_, 1, v_a_1114_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v___x_1118_);
v___x_1120_ = v___x_1116_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
else
{
lean_dec_ref(v_decl_1095_);
return v___x_1113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(lean_object* v_k_1125_, lean_object* v_fvarId_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v___x_1133_; lean_object* v_subst_1134_; lean_object* v_jpParamMask_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1146_; 
v___x_1133_ = lean_st_ref_take(v_a_1127_);
v_subst_1134_ = lean_ctor_get(v___x_1133_, 0);
v_jpParamMask_1135_ = lean_ctor_get(v___x_1133_, 1);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1137_ = v___x_1133_;
v_isShared_1138_ = v_isSharedCheck_1146_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_jpParamMask_1135_);
lean_inc(v_subst_1134_);
lean_dec(v___x_1133_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1146_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1139_ = lean_box(0);
v___x_1140_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1134_, v_fvarId_1126_, v___x_1139_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1140_);
v___x_1142_ = v___x_1137_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_jpParamMask_1135_);
v___x_1142_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = lean_st_ref_put(v_a_1127_, v___x_1142_);
v___x_1144_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1125_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_);
return v___x_1144_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(lean_object* v_decl_1148_, lean_object* v_k_1149_, lean_object* v_name_1150_, lean_object* v_numParams_1151_, lean_object* v_args_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v_fvarId_1159_; lean_object* v_binderName_1160_; lean_object* v_type_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1223_; 
v_fvarId_1159_ = lean_ctor_get(v_decl_1148_, 0);
v_binderName_1160_ = lean_ctor_get(v_decl_1148_, 1);
v_type_1161_ = lean_ctor_get(v_decl_1148_, 2);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_decl_1148_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; 
v_unused_1224_ = lean_ctor_get(v_decl_1148_, 3);
lean_dec(v_unused_1224_);
v___x_1163_ = v_decl_1148_;
v_isShared_1164_ = v_isSharedCheck_1223_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_type_1161_);
lean_inc(v_binderName_1160_);
lean_inc(v_fvarId_1159_);
lean_dec(v_decl_1148_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1223_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1161_, v_a_1156_, v_a_1157_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
v___x_1167_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1151_);
v___x_1168_ = l_Array_extract___redArg(v_args_1152_, v___x_1167_, v_numParams_1151_);
v___x_1169_ = 1;
v___x_1170_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___closed__0));
lean_inc(v_binderName_1160_);
v___x_1171_ = l_Lean_Name_str___override(v_binderName_1160_, v___x_1170_);
v___x_1172_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
v___x_1173_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_1173_, 0, v_name_1150_);
lean_ctor_set(v___x_1173_, 1, v___x_1168_);
v___x_1174_ = l_Lean_Compiler_LCNF_mkLetDecl(v___x_1169_, v___x_1171_, v___x_1172_, v___x_1173_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v_fvarId_1176_; lean_object* v___x_1177_; lean_object* v_lctx_1178_; lean_object* v_nextIdx_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1206_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1174_, 1);
v_fvarId_1176_ = lean_ctor_get(v_a_1175_, 0);
v___x_1177_ = lean_st_ref_take(v_a_1155_);
v_lctx_1178_ = lean_ctor_get(v___x_1177_, 0);
v_nextIdx_1179_ = lean_ctor_get(v___x_1177_, 1);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1181_ = v___x_1177_;
v_isShared_1182_ = v_isSharedCheck_1206_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_nextIdx_1179_);
lean_inc(v_lctx_1178_);
lean_dec(v___x_1177_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1206_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1183_ = lean_array_get_size(v_args_1152_);
v___x_1184_ = l_Array_extract___redArg(v_args_1152_, v_numParams_1151_, v___x_1183_);
lean_inc(v_fvarId_1176_);
v___x_1185_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1185_, 0, v_fvarId_1176_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_a_1166_);
lean_dec(v_a_1166_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 3, v___x_1185_);
lean_ctor_set(v___x_1163_, 2, v___x_1186_);
v___x_1188_ = v___x_1163_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_fvarId_1159_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_binderName_1160_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1205_, 3, v___x_1185_);
v___x_1188_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
lean_inc_ref(v___x_1188_);
v___x_1189_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1169_, v_lctx_1178_, v___x_1188_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1189_);
v___x_1191_ = v___x_1181_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_nextIdx_1179_);
v___x_1191_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = lean_st_ref_put(v_a_1155_, v___x_1191_);
v___x_1193_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1149_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1203_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1196_ = v___x_1193_;
v_isShared_1197_ = v_isSharedCheck_1203_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1193_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1203_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1188_);
lean_ctor_set(v___x_1198_, 1, v_a_1194_);
v___x_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1199_, 0, v_a_1175_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1199_);
v___x_1201_ = v___x_1196_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
else
{
lean_dec_ref(v___x_1188_);
lean_dec(v_a_1175_);
return v___x_1193_;
}
}
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_dec(v_a_1166_);
lean_del_object(v___x_1163_);
lean_dec(v_binderName_1160_);
lean_dec(v_fvarId_1159_);
lean_dec(v_numParams_1151_);
lean_dec_ref(v_k_1149_);
v_a_1207_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1174_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1174_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_del_object(v___x_1163_);
lean_dec(v_binderName_1160_);
lean_dec(v_fvarId_1159_);
lean_dec(v_numParams_1151_);
lean_dec(v_name_1150_);
lean_dec_ref(v_k_1149_);
v_a_1215_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1165_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1165_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(lean_object* v_decl_1225_, lean_object* v_k_1226_, lean_object* v_name_1227_, lean_object* v_args_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v_fvarId_1235_; lean_object* v_binderName_1236_; lean_object* v_type_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1256_; 
v_fvarId_1235_ = lean_ctor_get(v_decl_1225_, 0);
v_binderName_1236_ = lean_ctor_get(v_decl_1225_, 1);
v_type_1237_ = lean_ctor_get(v_decl_1225_, 2);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_decl_1225_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; 
v_unused_1257_ = lean_ctor_get(v_decl_1225_, 3);
lean_dec(v_unused_1257_);
v___x_1239_ = v_decl_1225_;
v_isShared_1240_ = v_isSharedCheck_1256_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_type_1237_);
lean_inc(v_binderName_1236_);
lean_inc(v_fvarId_1235_);
lean_dec(v_decl_1225_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1256_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1237_, v_a_1232_, v_a_1233_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1243_; lean_object* v___x_1245_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1241_, 1);
v___x_1243_ = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(v___x_1243_, 0, v_name_1227_);
lean_ctor_set(v___x_1243_, 1, v_args_1228_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 3, v___x_1243_);
lean_ctor_set(v___x_1239_, 2, v_a_1242_);
v___x_1245_ = v___x_1239_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_fvarId_1235_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_binderName_1236_);
lean_ctor_set(v_reuseFailAlloc_1247_, 2, v_a_1242_);
lean_ctor_set(v_reuseFailAlloc_1247_, 3, v___x_1243_);
v___x_1245_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v___x_1246_; 
v___x_1246_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1226_, v___x_1245_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
return v___x_1246_;
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_del_object(v___x_1239_);
lean_dec(v_binderName_1236_);
lean_dec(v_fvarId_1235_);
lean_dec_ref(v_args_1228_);
lean_dec(v_name_1227_);
lean_dec_ref(v_k_1226_);
v_a_1248_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1241_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1241_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(lean_object* v_decl_1258_, lean_object* v_k_1259_, lean_object* v_name_1260_, lean_object* v_args_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v_fvarId_1268_; lean_object* v_binderName_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1279_; 
v_fvarId_1268_ = lean_ctor_get(v_decl_1258_, 0);
v_binderName_1269_ = lean_ctor_get(v_decl_1258_, 1);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_decl_1258_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; lean_object* v_unused_1281_; 
v_unused_1280_ = lean_ctor_get(v_decl_1258_, 3);
lean_dec(v_unused_1280_);
v_unused_1281_ = lean_ctor_get(v_decl_1258_, 2);
lean_dec(v_unused_1281_);
v___x_1271_ = v_decl_1258_;
v_isShared_1272_ = v_isSharedCheck_1279_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_binderName_1269_);
lean_inc(v_fvarId_1268_);
lean_dec(v_decl_1258_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1279_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1273_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__8);
v___x_1274_ = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(v___x_1274_, 0, v_name_1260_);
lean_ctor_set(v___x_1274_, 1, v_args_1261_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 3, v___x_1274_);
lean_ctor_set(v___x_1271_, 2, v___x_1273_);
v___x_1276_ = v___x_1271_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_fvarId_1268_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_binderName_1269_);
lean_ctor_set(v_reuseFailAlloc_1278_, 2, v___x_1273_);
lean_ctor_set(v_reuseFailAlloc_1278_, 3, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1277_; 
v___x_1277_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1259_, v___x_1276_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_);
return v___x_1277_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(lean_object* v_decl_1282_, lean_object* v_k_1283_, lean_object* v_name_1284_, lean_object* v_numParams_1285_, lean_object* v_args_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v_numArgs_1293_; uint8_t v___x_1294_; 
v_numArgs_1293_ = lean_array_get_size(v_args_1286_);
v___x_1294_ = lean_nat_dec_lt(v_numArgs_1293_, v_numParams_1285_);
if (v___x_1294_ == 0)
{
uint8_t v___x_1295_; 
v___x_1295_ = lean_nat_dec_eq(v_numArgs_1293_, v_numParams_1285_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; 
v___x_1296_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(v_decl_1282_, v_k_1283_, v_name_1284_, v_numParams_1285_, v_args_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
lean_dec_ref(v_args_1286_);
return v___x_1296_;
}
else
{
lean_object* v___x_1297_; 
lean_dec(v_numParams_1285_);
v___x_1297_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_1282_, v_k_1283_, v_name_1284_, v_args_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
return v___x_1297_;
}
}
else
{
lean_object* v___x_1298_; 
lean_dec(v_numParams_1285_);
v___x_1298_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(v_decl_1282_, v_k_1283_, v_name_1284_, v_args_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
return v___x_1298_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4(void){
_start:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1300_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__3));
v___x_1301_ = lean_unsigned_to_nat(14u);
v___x_1302_ = lean_unsigned_to_nat(185u);
v___x_1303_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__0));
v___x_1304_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1305_ = l_mkPanicMessageWithDecl(v___x_1304_, v___x_1303_, v___x_1302_, v___x_1301_, v___x_1300_);
return v___x_1305_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__2);
v___x_1313_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(lean_object* v_decl_1322_, lean_object* v_k_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___x_1338_; lean_object* v_fvarId_1339_; lean_object* v_binderName_1340_; lean_object* v_type_1341_; lean_object* v_value_1342_; lean_object* v_subst_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1795_; 
v___x_1338_ = lean_st_ref_get(v_a_1324_);
v_fvarId_1339_ = lean_ctor_get(v_decl_1322_, 0);
v_binderName_1340_ = lean_ctor_get(v_decl_1322_, 1);
v_type_1341_ = lean_ctor_get(v_decl_1322_, 2);
v_value_1342_ = lean_ctor_get(v_decl_1322_, 3);
v_subst_1343_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1795_ == 0)
{
lean_object* v_unused_1796_; 
v_unused_1796_ = lean_ctor_get(v___x_1338_, 1);
lean_dec(v_unused_1796_);
v___x_1345_ = v___x_1338_;
v_isShared_1346_ = v_isSharedCheck_1795_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_subst_1343_);
lean_dec(v___x_1338_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1795_;
goto v_resetjp_1344_;
}
v___jp_1330_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__2);
v___x_1337_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1336_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
return v___x_1337_;
}
v_resetjp_1344_:
{
uint8_t v___x_1347_; uint8_t v___x_1348_; lean_object* v___x_1349_; 
v___x_1347_ = 0;
v___x_1348_ = 1;
lean_inc(v_value_1342_);
v___x_1349_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(v___x_1347_, v_subst_1343_, v_value_1342_, v___x_1348_);
lean_dec_ref(v_subst_1343_);
switch(lean_obj_tag(v___x_1349_))
{
case 0:
{
lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1366_; 
lean_inc(v_binderName_1340_);
lean_inc(v_fvarId_1339_);
lean_del_object(v___x_1345_);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_decl_1322_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; lean_object* v_unused_1368_; lean_object* v_unused_1369_; lean_object* v_unused_1370_; 
v_unused_1367_ = lean_ctor_get(v_decl_1322_, 3);
lean_dec(v_unused_1367_);
v_unused_1368_ = lean_ctor_get(v_decl_1322_, 2);
lean_dec(v_unused_1368_);
v_unused_1369_ = lean_ctor_get(v_decl_1322_, 1);
lean_dec(v_unused_1369_);
v_unused_1370_ = lean_ctor_get(v_decl_1322_, 0);
lean_dec(v_unused_1370_);
v___x_1351_ = v_decl_1322_;
v_isShared_1352_ = v_isSharedCheck_1366_;
goto v_resetjp_1350_;
}
else
{
lean_dec(v_decl_1322_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1366_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v_value_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1365_; 
v_value_1353_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1355_ = v___x_1349_;
v_isShared_1356_ = v_isSharedCheck_1365_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_value_1353_);
lean_dec(v___x_1349_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1365_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType(v_value_1353_);
if (v_isShared_1356_ == 0)
{
v___x_1359_ = v___x_1355_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_value_1353_);
v___x_1359_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
lean_object* v___x_1361_; 
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 3, v___x_1359_);
lean_ctor_set(v___x_1351_, 2, v___x_1357_);
v___x_1361_ = v___x_1351_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_fvarId_1339_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_binderName_1340_);
lean_ctor_set(v_reuseFailAlloc_1363_, 2, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1363_, 3, v___x_1359_);
v___x_1361_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
lean_object* v___x_1362_; 
v___x_1362_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1323_, v___x_1361_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1362_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1371_; 
lean_inc(v_fvarId_1339_);
lean_del_object(v___x_1345_);
lean_dec_ref(v_decl_1322_);
v___x_1371_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_1323_, v_fvarId_1339_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1371_;
}
case 2:
{
lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1474_; 
lean_inc(v_binderName_1340_);
lean_inc(v_fvarId_1339_);
lean_del_object(v___x_1345_);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_decl_1322_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; lean_object* v_unused_1476_; lean_object* v_unused_1477_; lean_object* v_unused_1478_; 
v_unused_1475_ = lean_ctor_get(v_decl_1322_, 3);
lean_dec(v_unused_1475_);
v_unused_1476_ = lean_ctor_get(v_decl_1322_, 2);
lean_dec(v_unused_1476_);
v_unused_1477_ = lean_ctor_get(v_decl_1322_, 1);
lean_dec(v_unused_1477_);
v_unused_1478_ = lean_ctor_get(v_decl_1322_, 0);
lean_dec(v_unused_1478_);
v___x_1373_ = v_decl_1322_;
v_isShared_1374_ = v_isSharedCheck_1474_;
goto v_resetjp_1372_;
}
else
{
lean_dec(v_decl_1322_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1474_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v_typeName_1375_; lean_object* v_idx_1376_; lean_object* v_struct_1377_; lean_object* v___x_1378_; 
v_typeName_1375_ = lean_ctor_get(v___x_1349_, 0);
lean_inc_n(v_typeName_1375_, 2);
v_idx_1376_ = lean_ctor_get(v___x_1349_, 1);
lean_inc(v_idx_1376_);
v_struct_1377_ = lean_ctor_get(v___x_1349_, 2);
lean_inc(v_struct_1377_);
lean_dec_ref_known(v___x_1349_, 3);
v___x_1378_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_typeName_1375_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref_known(v___x_1378_, 1);
if (lean_obj_tag(v_a_1379_) == 1)
{
lean_object* v_val_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1416_; 
lean_dec(v_typeName_1375_);
lean_del_object(v___x_1373_);
lean_dec(v_binderName_1340_);
v_val_1380_ = lean_ctor_get(v_a_1379_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_a_1379_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1382_ = v_a_1379_;
v_isShared_1383_ = v_isSharedCheck_1416_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_val_1380_);
lean_dec(v_a_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1416_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v_fieldIdx_1384_; uint8_t v___x_1385_; 
v_fieldIdx_1384_ = lean_ctor_get(v_val_1380_, 2);
lean_inc(v_fieldIdx_1384_);
lean_dec(v_val_1380_);
v___x_1385_ = lean_nat_dec_eq(v_fieldIdx_1384_, v_idx_1376_);
lean_dec(v_idx_1376_);
lean_dec(v_fieldIdx_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v_subst_1387_; lean_object* v_jpParamMask_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1399_; 
lean_del_object(v___x_1382_);
lean_dec(v_struct_1377_);
v___x_1386_ = lean_st_ref_take(v_a_1324_);
v_subst_1387_ = lean_ctor_get(v___x_1386_, 0);
v_jpParamMask_1388_ = lean_ctor_get(v___x_1386_, 1);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1390_ = v___x_1386_;
v_isShared_1391_ = v_isSharedCheck_1399_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_jpParamMask_1388_);
lean_inc(v_subst_1387_);
lean_dec(v___x_1386_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1399_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1392_ = lean_box(0);
v___x_1393_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1387_, v_fvarId_1339_, v___x_1392_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1393_);
v___x_1395_ = v___x_1390_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_jpParamMask_1388_);
v___x_1395_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1396_ = lean_st_ref_put(v_a_1324_, v___x_1395_);
v___x_1397_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1397_;
}
}
}
else
{
lean_object* v___x_1400_; lean_object* v_subst_1401_; lean_object* v_jpParamMask_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1415_; 
v___x_1400_ = lean_st_ref_take(v_a_1324_);
v_subst_1401_ = lean_ctor_get(v___x_1400_, 0);
v_jpParamMask_1402_ = lean_ctor_get(v___x_1400_, 1);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1404_ = v___x_1400_;
v_isShared_1405_ = v_isSharedCheck_1415_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_jpParamMask_1402_);
lean_inc(v_subst_1401_);
lean_dec(v___x_1400_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1415_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v_struct_1377_);
v___x_1407_ = v___x_1382_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_struct_1377_);
v___x_1407_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1408_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1401_, v_fvarId_1339_, v___x_1407_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1408_);
v___x_1410_ = v___x_1404_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_jpParamMask_1402_);
v___x_1410_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = lean_st_ref_put(v_a_1324_, v___x_1410_);
v___x_1412_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1412_;
}
}
}
}
}
}
else
{
lean_object* v___x_1417_; lean_object* v_subst_1418_; lean_object* v___x_1419_; 
lean_dec(v_a_1379_);
v___x_1417_ = lean_st_ref_get(v_a_1324_);
v_subst_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc_ref(v_subst_1418_);
lean_dec(v___x_1417_);
v___x_1419_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_1418_, v_struct_1377_, v___x_1348_);
lean_dec_ref(v_subst_1418_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_fvarId_1420_; lean_object* v___x_1421_; lean_object* v_env_1422_; uint8_t v___x_1423_; lean_object* v___x_1424_; 
v_fvarId_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_fvarId_1420_);
lean_dec_ref_known(v___x_1419_, 1);
v___x_1421_ = lean_st_ref_get(v_a_1328_);
v_env_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc_ref(v_env_1422_);
lean_dec(v___x_1421_);
v___x_1423_ = 0;
v___x_1424_ = l_Lean_Environment_find_x3f(v_env_1422_, v_typeName_1375_, v___x_1423_);
if (lean_obj_tag(v___x_1424_) == 1)
{
lean_object* v_val_1425_; 
v_val_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_val_1425_);
lean_dec_ref_known(v___x_1424_, 1);
if (lean_obj_tag(v_val_1425_) == 5)
{
lean_object* v_val_1426_; lean_object* v_ctors_1427_; 
v_val_1426_ = lean_ctor_get(v_val_1425_, 0);
lean_inc_ref(v_val_1426_);
lean_dec_ref_known(v_val_1425_, 1);
v_ctors_1427_ = lean_ctor_get(v_val_1426_, 4);
lean_inc(v_ctors_1427_);
lean_dec_ref(v_val_1426_);
if (lean_obj_tag(v_ctors_1427_) == 1)
{
lean_object* v_tail_1428_; 
v_tail_1428_ = lean_ctor_get(v_ctors_1427_, 1);
if (lean_obj_tag(v_tail_1428_) == 0)
{
lean_object* v_head_1429_; lean_object* v___x_1430_; 
v_head_1429_ = lean_ctor_get(v_ctors_1427_, 0);
lean_inc(v_head_1429_);
lean_dec_ref_known(v_ctors_1427_, 2);
v___x_1430_ = l_Lean_Compiler_LCNF_getCtorLayout(v_head_1429_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v_ctorInfo_1432_; lean_object* v_fieldInfo_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v_fst_1437_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v_ctorInfo_1432_ = lean_ctor_get(v_a_1431_, 0);
lean_inc_ref(v_ctorInfo_1432_);
v_fieldInfo_1433_ = lean_ctor_get(v_a_1431_, 1);
lean_inc_ref(v_fieldInfo_1433_);
lean_dec(v_a_1431_);
v___x_1434_ = lean_box(0);
v___x_1435_ = lean_array_get(v___x_1434_, v_fieldInfo_1433_, v_idx_1376_);
lean_dec(v_idx_1376_);
lean_dec_ref(v_fieldInfo_1433_);
v___x_1436_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_fvarId_1420_, v_ctorInfo_1432_, v___x_1435_);
lean_dec_ref(v_ctorInfo_1432_);
v_fst_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_fst_1437_);
if (lean_obj_tag(v_fst_1437_) == 1)
{
lean_object* v___x_1438_; 
lean_dec_ref(v___x_1436_);
lean_del_object(v___x_1373_);
lean_dec(v_binderName_1340_);
v___x_1438_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_1323_, v_fvarId_1339_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1438_;
}
else
{
lean_object* v_snd_1439_; lean_object* v___x_1441_; 
v_snd_1439_ = lean_ctor_get(v___x_1436_, 1);
lean_inc(v_snd_1439_);
lean_dec_ref(v___x_1436_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 3, v_fst_1437_);
lean_ctor_set(v___x_1373_, 2, v_snd_1439_);
v___x_1441_ = v___x_1373_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_fvarId_1339_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_binderName_1340_);
lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_snd_1439_);
lean_ctor_set(v_reuseFailAlloc_1443_, 3, v_fst_1437_);
v___x_1441_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1442_; 
v___x_1442_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1323_, v___x_1441_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1442_;
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec(v_fvarId_1420_);
lean_dec(v_idx_1376_);
lean_del_object(v___x_1373_);
lean_dec(v_binderName_1340_);
lean_dec(v_fvarId_1339_);
lean_dec_ref(v_k_1323_);
v_a_1444_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1430_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1430_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_1427_, 2);
lean_dec(v_fvarId_1420_);
lean_dec(v_idx_1376_);
lean_del_object(v___x_1373_);
lean_dec(v_binderName_1340_);
lean_dec(v_fvarId_1339_);
lean_dec_ref(v_k_1323_);
v___y_1331_ = v_a_1324_;
v___y_1332_ = v_a_1325_;
v___y_1333_ = v_a_1326_;
v___y_1334_ = v_a_1327_;
v___y_1335_ = v_a_1328_;
goto v___jp_1330_;
}
}
else
{
lean_dec(v_ctors_1427_);
lean_dec(v_fvarId_1420_);
lean_dec(v_idx_1376_);
lean_del_object(v___x_1373_);
lean_dec(v_binderName_1340_);
lean_dec(v_fvarId_1339_);
lean_dec_ref(v_k_1323_);
v___y_1331_ = v_a_1324_;
v___y_1332_ = v_a_1325_;
v___y_1333_ = v_a_1326_;
v___y_1334_ = v_a_1327_;
v___y_1335_ = v_a_1328_;
goto v___jp_1330_;
}
}
else
{
lean_dec(v_val_1425_);
lean_dec(v_fvarId_1420_);
lean_dec(v_idx_1376_);
lean_del_object(v___x_1373_);
lean_dec(v_binderName_1340_);
lean_dec(v_fvarId_1339_);
lean_dec_ref(v_k_1323_);
v___y_1331_ = v_a_1324_;
v___y_1332_ = v_a_1325_;
v___y_1333_ = v_a_1326_;
v___y_1334_ = v_a_1327_;
v___y_1335_ = v_a_1328_;
goto v___jp_1330_;
}
}
else
{
lean_dec(v___x_1424_);
lean_dec(v_fvarId_1420_);
lean_dec(v_idx_1376_);
lean_del_object(v___x_1373_);
lean_dec(v_binderName_1340_);
lean_dec(v_fvarId_1339_);
lean_dec_ref(v_k_1323_);
v___y_1331_ = v_a_1324_;
v___y_1332_ = v_a_1325_;
v___y_1333_ = v_a_1326_;
v___y_1334_ = v_a_1327_;
v___y_1335_ = v_a_1328_;
goto v___jp_1330_;
}
}
else
{
lean_object* v___x_1452_; lean_object* v_subst_1453_; lean_object* v_jpParamMask_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1465_; 
lean_dec(v_idx_1376_);
lean_dec(v_typeName_1375_);
lean_del_object(v___x_1373_);
lean_dec(v_binderName_1340_);
v___x_1452_ = lean_st_ref_take(v_a_1324_);
v_subst_1453_ = lean_ctor_get(v___x_1452_, 0);
v_jpParamMask_1454_ = lean_ctor_get(v___x_1452_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1456_ = v___x_1452_;
v_isShared_1457_ = v_isSharedCheck_1465_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_jpParamMask_1454_);
lean_inc(v_subst_1453_);
lean_dec(v___x_1452_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1465_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1458_ = lean_box(0);
v___x_1459_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1453_, v_fvarId_1339_, v___x_1458_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1459_);
v___x_1461_ = v___x_1456_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_jpParamMask_1454_);
v___x_1461_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = lean_st_ref_put(v_a_1324_, v___x_1461_);
v___x_1463_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1463_;
}
}
}
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_dec(v_struct_1377_);
lean_dec(v_idx_1376_);
lean_dec(v_typeName_1375_);
lean_del_object(v___x_1373_);
lean_dec(v_binderName_1340_);
lean_dec(v_fvarId_1339_);
lean_dec_ref(v_k_1323_);
v_a_1466_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1378_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1378_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
}
case 3:
{
lean_object* v_declName_1479_; lean_object* v_args_1480_; size_t v_sz_1481_; size_t v___x_1482_; lean_object* v___x_1483_; 
v_declName_1479_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_declName_1479_);
v_args_1480_ = lean_ctor_get(v___x_1349_, 2);
lean_inc_ref_n(v_args_1480_, 2);
lean_dec_ref_known(v___x_1349_, 3);
v_sz_1481_ = lean_array_size(v_args_1480_);
v___x_1482_ = ((size_t)0ULL);
v___x_1483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_1481_, v___x_1482_, v_args_1480_, v_a_1324_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1485_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref_known(v___x_1483_, 1);
lean_inc(v_declName_1479_);
v___x_1485_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_1479_, v_a_1328_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_a_1486_);
lean_dec_ref_known(v___x_1485_, 1);
if (lean_obj_tag(v_a_1486_) == 1)
{
lean_object* v_val_1487_; lean_object* v_params_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_dec_ref(v_args_1480_);
lean_del_object(v___x_1345_);
v_val_1487_ = lean_ctor_get(v_a_1486_, 0);
lean_inc(v_val_1487_);
lean_dec_ref_known(v_a_1486_, 1);
v_params_1488_ = lean_ctor_get(v_val_1487_, 3);
lean_inc_ref(v_params_1488_);
lean_dec(v_val_1487_);
v___x_1489_ = lean_array_get_size(v_params_1488_);
lean_dec_ref(v_params_1488_);
v___x_1490_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_1322_, v_k_1323_, v_declName_1479_, v___x_1489_, v_a_1484_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1490_;
}
else
{
lean_object* v___x_1491_; 
lean_dec(v_a_1486_);
lean_inc(v_declName_1479_);
v___x_1491_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_1479_, v_a_1328_);
if (lean_obj_tag(v___x_1491_) == 0)
{
lean_object* v_a_1492_; 
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref_known(v___x_1491_, 1);
if (lean_obj_tag(v_a_1492_) == 1)
{
lean_object* v_val_1493_; lean_object* v_toSignature_1494_; lean_object* v_params_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
lean_dec_ref(v_args_1480_);
lean_del_object(v___x_1345_);
v_val_1493_ = lean_ctor_get(v_a_1492_, 0);
lean_inc(v_val_1493_);
lean_dec_ref_known(v_a_1492_, 1);
v_toSignature_1494_ = lean_ctor_get(v_val_1493_, 0);
lean_inc_ref(v_toSignature_1494_);
lean_dec(v_val_1493_);
v_params_1495_ = lean_ctor_get(v_toSignature_1494_, 3);
lean_inc_ref(v_params_1495_);
lean_dec_ref(v_toSignature_1494_);
v___x_1496_ = lean_array_get_size(v_params_1495_);
lean_dec_ref(v_params_1495_);
v___x_1497_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_1322_, v_k_1323_, v_declName_1479_, v___x_1496_, v_a_1484_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1497_;
}
else
{
lean_object* v___x_1498_; lean_object* v_env_1499_; uint8_t v___x_1500_; lean_object* v___x_1501_; 
lean_dec(v_a_1492_);
v___x_1498_ = lean_st_ref_get(v_a_1328_);
v_env_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc_ref(v_env_1499_);
lean_dec(v___x_1498_);
v___x_1500_ = 0;
lean_inc(v_declName_1479_);
v___x_1501_ = l_Lean_Environment_find_x3f(v_env_1499_, v_declName_1479_, v___x_1500_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
lean_dec(v_a_1484_);
lean_dec_ref(v_args_1480_);
lean_dec(v_declName_1479_);
lean_del_object(v___x_1345_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_decl_1322_);
v___x_1502_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__4);
v___x_1503_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1502_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1503_;
}
else
{
lean_object* v_val_1504_; 
v_val_1504_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_val_1504_);
lean_dec_ref_known(v___x_1501_, 1);
switch(lean_obj_tag(v_val_1504_))
{
case 0:
{
lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1520_; 
lean_dec(v_a_1484_);
lean_dec_ref(v_args_1480_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_decl_1322_);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_val_1504_);
if (v_isSharedCheck_1520_ == 0)
{
lean_object* v_unused_1521_; 
v_unused_1521_ = lean_ctor_get(v_val_1504_, 0);
lean_dec(v_unused_1521_);
v___x_1506_ = v_val_1504_;
v_isShared_1507_ = v_isSharedCheck_1520_;
goto v_resetjp_1505_;
}
else
{
lean_dec(v_val_1504_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1520_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1511_; 
v___x_1508_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1509_ = l_Lean_Name_toString(v_declName_1479_, v___x_1348_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set_tag(v___x_1506_, 3);
lean_ctor_set(v___x_1506_, 0, v___x_1509_);
v___x_1511_ = v___x_1506_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1513_; 
if (v_isShared_1346_ == 0)
{
lean_ctor_set_tag(v___x_1345_, 5);
lean_ctor_set(v___x_1345_, 1, v___x_1511_);
lean_ctor_set(v___x_1345_, 0, v___x_1508_);
v___x_1513_ = v___x_1345_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1508_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1514_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1515_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1513_);
lean_ctor_set(v___x_1515_, 1, v___x_1514_);
v___x_1516_ = l_Lean_MessageData_ofFormat(v___x_1515_);
v___x_1517_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1516_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1517_;
}
}
}
}
case 2:
{
lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1537_; 
lean_dec(v_a_1484_);
lean_dec_ref(v_args_1480_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_decl_1322_);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_val_1504_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; 
v_unused_1538_ = lean_ctor_get(v_val_1504_, 0);
lean_dec(v_unused_1538_);
v___x_1523_ = v_val_1504_;
v_isShared_1524_ = v_isSharedCheck_1537_;
goto v_resetjp_1522_;
}
else
{
lean_dec(v_val_1504_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1537_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1528_; 
v___x_1525_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1526_ = l_Lean_Name_toString(v_declName_1479_, v___x_1348_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set_tag(v___x_1523_, 3);
lean_ctor_set(v___x_1523_, 0, v___x_1526_);
v___x_1528_ = v___x_1523_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1526_);
v___x_1528_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1530_; 
if (v_isShared_1346_ == 0)
{
lean_ctor_set_tag(v___x_1345_, 5);
lean_ctor_set(v___x_1345_, 1, v___x_1528_);
lean_ctor_set(v___x_1345_, 0, v___x_1525_);
v___x_1530_ = v___x_1345_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1531_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1530_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = l_Lean_MessageData_ofFormat(v___x_1532_);
v___x_1534_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1533_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1534_;
}
}
}
}
case 4:
{
lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1554_; 
lean_dec(v_a_1484_);
lean_dec_ref(v_args_1480_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_decl_1322_);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_val_1504_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; 
v_unused_1555_ = lean_ctor_get(v_val_1504_, 0);
lean_dec(v_unused_1555_);
v___x_1540_ = v_val_1504_;
v_isShared_1541_ = v_isSharedCheck_1554_;
goto v_resetjp_1539_;
}
else
{
lean_dec(v_val_1504_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1554_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1545_; 
v___x_1542_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1543_ = l_Lean_Name_toString(v_declName_1479_, v___x_1348_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set_tag(v___x_1540_, 3);
lean_ctor_set(v___x_1540_, 0, v___x_1543_);
v___x_1545_ = v___x_1540_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_object* v___x_1547_; 
if (v_isShared_1346_ == 0)
{
lean_ctor_set_tag(v___x_1345_, 5);
lean_ctor_set(v___x_1345_, 1, v___x_1545_);
lean_ctor_set(v___x_1345_, 0, v___x_1542_);
v___x_1547_ = v___x_1345_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1548_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = l_Lean_MessageData_ofFormat(v___x_1549_);
v___x_1551_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1550_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1551_;
}
}
}
}
case 5:
{
lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1571_; 
lean_dec(v_a_1484_);
lean_dec_ref(v_args_1480_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_decl_1322_);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_val_1504_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; 
v_unused_1572_ = lean_ctor_get(v_val_1504_, 0);
lean_dec(v_unused_1572_);
v___x_1557_ = v_val_1504_;
v_isShared_1558_ = v_isSharedCheck_1571_;
goto v_resetjp_1556_;
}
else
{
lean_dec(v_val_1504_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1571_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1562_; 
v___x_1559_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__6));
v___x_1560_ = l_Lean_Name_toString(v_declName_1479_, v___x_1348_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set_tag(v___x_1557_, 3);
lean_ctor_set(v___x_1557_, 0, v___x_1560_);
v___x_1562_ = v___x_1557_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
lean_object* v___x_1564_; 
if (v_isShared_1346_ == 0)
{
lean_ctor_set_tag(v___x_1345_, 5);
lean_ctor_set(v___x_1345_, 1, v___x_1562_);
lean_ctor_set(v___x_1345_, 0, v___x_1559_);
v___x_1564_ = v___x_1345_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1565_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__8));
v___x_1566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1564_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = l_Lean_MessageData_ofFormat(v___x_1566_);
v___x_1568_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1567_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1568_;
}
}
}
}
case 6:
{
lean_object* v_val_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1708_; 
v_val_1573_ = lean_ctor_get(v_val_1504_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_val_1504_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1575_ = v_val_1504_;
v_isShared_1576_ = v_isSharedCheck_1708_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_val_1573_);
lean_dec(v_val_1504_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1708_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v_induct_1577_; lean_object* v_cidx_1578_; lean_object* v_numParams_1579_; lean_object* v___x_1580_; 
v_induct_1577_ = lean_ctor_get(v_val_1573_, 1);
lean_inc_n(v_induct_1577_, 2);
v_cidx_1578_ = lean_ctor_get(v_val_1573_, 2);
lean_inc(v_cidx_1578_);
v_numParams_1579_ = lean_ctor_get(v_val_1573_, 3);
lean_inc(v_numParams_1579_);
lean_dec_ref(v_val_1573_);
v___x_1580_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_induct_1577_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1580_, 1);
if (lean_obj_tag(v_a_1581_) == 1)
{
lean_object* v_val_1582_; lean_object* v___x_1583_; lean_object* v_numParams_1584_; lean_object* v_fieldIdx_1585_; lean_object* v_subst_1586_; lean_object* v_jpParamMask_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1600_; 
lean_inc(v_fvarId_1339_);
lean_dec(v_numParams_1579_);
lean_dec(v_cidx_1578_);
lean_dec(v_induct_1577_);
lean_del_object(v___x_1575_);
lean_dec(v_a_1484_);
lean_dec(v_declName_1479_);
lean_del_object(v___x_1345_);
lean_dec_ref(v_decl_1322_);
v_val_1582_ = lean_ctor_get(v_a_1581_, 0);
lean_inc(v_val_1582_);
lean_dec_ref_known(v_a_1581_, 1);
v___x_1583_ = lean_st_ref_take(v_a_1324_);
v_numParams_1584_ = lean_ctor_get(v_val_1582_, 1);
lean_inc(v_numParams_1584_);
v_fieldIdx_1585_ = lean_ctor_get(v_val_1582_, 2);
lean_inc(v_fieldIdx_1585_);
lean_dec(v_val_1582_);
v_subst_1586_ = lean_ctor_get(v___x_1583_, 0);
v_jpParamMask_1587_ = lean_ctor_get(v___x_1583_, 1);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1589_ = v___x_1583_;
v_isShared_1590_ = v_isSharedCheck_1600_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_jpParamMask_1587_);
lean_inc(v_subst_1586_);
lean_dec(v___x_1583_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1600_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1596_; 
v___x_1591_ = lean_box(0);
v___x_1592_ = lean_nat_add(v_numParams_1584_, v_fieldIdx_1585_);
lean_dec(v_fieldIdx_1585_);
lean_dec(v_numParams_1584_);
v___x_1593_ = lean_array_get(v___x_1591_, v_args_1480_, v___x_1592_);
lean_dec(v___x_1592_);
lean_dec_ref(v_args_1480_);
v___x_1594_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1586_, v_fvarId_1339_, v___x_1593_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v___x_1594_);
v___x_1596_ = v___x_1589_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_jpParamMask_1587_);
v___x_1596_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = lean_st_ref_put(v_a_1324_, v___x_1596_);
v___x_1598_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1598_;
}
}
}
else
{
lean_object* v___x_1601_; 
lean_dec(v_a_1581_);
lean_dec_ref(v_args_1480_);
v___x_1601_ = l_Lean_Compiler_LCNF_nameToImpureType(v_induct_1577_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; uint8_t v___x_1603_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1601_, 1);
v___x_1603_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_1602_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; 
lean_dec(v_a_1602_);
lean_dec(v_cidx_1578_);
lean_del_object(v___x_1575_);
v___x_1604_ = l_Lean_Compiler_LCNF_getCtorLayout(v_declName_1479_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1667_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1607_ = v___x_1604_;
v_isShared_1608_ = v_isSharedCheck_1667_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1604_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1667_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v_ctorInfo_1614_; lean_object* v_fieldInfo_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1666_; 
v_ctorInfo_1614_ = lean_ctor_get(v_a_1605_, 0);
v_fieldInfo_1615_ = lean_ctor_get(v_a_1605_, 1);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_a_1605_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1617_ = v_a_1605_;
v_isShared_1618_ = v_isSharedCheck_1666_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_fieldInfo_1615_);
lean_inc(v_ctorInfo_1614_);
lean_dec(v_a_1605_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1666_;
goto v_resetjp_1616_;
}
v___jp_1609_:
{
lean_object* v___x_1610_; lean_object* v___x_1612_; 
v___x_1610_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__9);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 0, v___x_1610_);
v___x_1612_ = v___x_1607_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
v_resetjp_1616_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; 
v___x_1619_ = lean_array_get_size(v_a_1484_);
v___x_1620_ = l_Array_extract___redArg(v_a_1484_, v_numParams_1579_, v___x_1619_);
lean_dec(v_a_1484_);
v___x_1621_ = lean_array_get_size(v___x_1620_);
v___x_1622_ = lean_array_get_size(v_fieldInfo_1615_);
v___x_1623_ = lean_nat_dec_eq(v___x_1621_, v___x_1622_);
if (v___x_1623_ == 0)
{
lean_dec_ref(v___x_1620_);
lean_del_object(v___x_1617_);
lean_dec_ref(v_fieldInfo_1615_);
lean_dec_ref(v_ctorInfo_1614_);
lean_del_object(v___x_1345_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_decl_1322_);
goto v___jp_1609_;
}
else
{
if (v___x_1603_ == 0)
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
lean_del_object(v___x_1607_);
v___x_1624_ = lean_unsigned_to_nat(0u);
v___x_1625_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4));
v___x_1626_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v___x_1622_, v_fieldInfo_1615_, v___x_1620_, v___x_1624_, v___x_1625_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1628_; lean_object* v_lctx_1629_; lean_object* v_nextIdx_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1657_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1626_, 1);
v___x_1628_ = lean_st_ref_take(v_a_1326_);
v_lctx_1629_ = lean_ctor_get(v___x_1628_, 0);
v_nextIdx_1630_ = lean_ctor_get(v___x_1628_, 1);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1632_ = v___x_1628_;
v_isShared_1633_ = v_isSharedCheck_1657_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_nextIdx_1630_);
lean_inc(v_lctx_1629_);
lean_dec(v___x_1628_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1657_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; uint8_t v___x_1635_; lean_object* v___x_1637_; 
v___x_1634_ = l_Lean_Compiler_LCNF_CtorInfo_type(v_ctorInfo_1614_);
v___x_1635_ = 1;
lean_inc_ref(v_ctorInfo_1614_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set_tag(v___x_1617_, 5);
lean_ctor_set(v___x_1617_, 1, v_a_1627_);
v___x_1637_ = v___x_1617_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_ctorInfo_1614_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_a_1627_);
v___x_1637_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1641_; 
lean_inc(v_binderName_1340_);
lean_inc(v_fvarId_1339_);
v___x_1638_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1638_, 0, v_fvarId_1339_);
lean_ctor_set(v___x_1638_, 1, v_binderName_1340_);
lean_ctor_set(v___x_1638_, 2, v___x_1634_);
lean_ctor_set(v___x_1638_, 3, v___x_1637_);
lean_inc_ref(v___x_1638_);
v___x_1639_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1635_, v_lctx_1629_, v___x_1638_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v___x_1639_);
v___x_1641_ = v___x_1632_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_nextIdx_1630_);
v___x_1641_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = lean_st_ref_put(v_a_1326_, v___x_1641_);
v___x_1643_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(v_decl_1322_, v_k_1323_, v_ctorInfo_1614_, v_fieldInfo_1615_, v___x_1620_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
lean_dec_ref(v___x_1620_);
lean_dec_ref(v_fieldInfo_1615_);
lean_dec_ref(v_ctorInfo_1614_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1654_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1654_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1654_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 1, v_a_1644_);
lean_ctor_set(v___x_1345_, 0, v___x_1638_);
v___x_1649_ = v___x_1345_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1638_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1651_; 
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1649_);
v___x_1651_ = v___x_1646_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1638_, 4);
lean_del_object(v___x_1345_);
return v___x_1643_;
}
}
}
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec_ref(v___x_1620_);
lean_del_object(v___x_1617_);
lean_dec_ref(v_fieldInfo_1615_);
lean_dec_ref(v_ctorInfo_1614_);
lean_del_object(v___x_1345_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_decl_1322_);
v_a_1658_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1626_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1626_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
else
{
lean_dec_ref(v___x_1620_);
lean_del_object(v___x_1617_);
lean_dec_ref(v_fieldInfo_1615_);
lean_dec_ref(v_ctorInfo_1614_);
lean_del_object(v___x_1345_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_decl_1322_);
goto v___jp_1609_;
}
}
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_dec(v_numParams_1579_);
lean_dec(v_a_1484_);
lean_del_object(v___x_1345_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_decl_1322_);
v_a_1668_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1604_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1604_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
else
{
lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1687_; 
lean_inc(v_binderName_1340_);
lean_inc(v_fvarId_1339_);
lean_dec(v_numParams_1579_);
lean_dec(v_a_1484_);
lean_dec(v_declName_1479_);
lean_del_object(v___x_1345_);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_decl_1322_);
if (v_isSharedCheck_1687_ == 0)
{
lean_object* v_unused_1688_; lean_object* v_unused_1689_; lean_object* v_unused_1690_; lean_object* v_unused_1691_; 
v_unused_1688_ = lean_ctor_get(v_decl_1322_, 3);
lean_dec(v_unused_1688_);
v_unused_1689_ = lean_ctor_get(v_decl_1322_, 2);
lean_dec(v_unused_1689_);
v_unused_1690_ = lean_ctor_get(v_decl_1322_, 1);
lean_dec(v_unused_1690_);
v_unused_1691_ = lean_ctor_get(v_decl_1322_, 0);
lean_dec(v_unused_1691_);
v___x_1677_ = v_decl_1322_;
v_isShared_1678_ = v_isSharedCheck_1687_;
goto v_resetjp_1676_;
}
else
{
lean_dec(v_decl_1322_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1687_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = l_Lean_Compiler_LCNF_LitValue_impureTypeScalarNumLit(v_a_1602_, v_cidx_1578_);
lean_dec(v_cidx_1578_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set_tag(v___x_1575_, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1679_);
v___x_1681_ = v___x_1575_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1683_; 
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 3, v___x_1681_);
lean_ctor_set(v___x_1677_, 2, v_a_1602_);
v___x_1683_ = v___x_1677_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_fvarId_1339_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_binderName_1340_);
lean_ctor_set(v_reuseFailAlloc_1685_, 2, v_a_1602_);
lean_ctor_set(v_reuseFailAlloc_1685_, 3, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1684_; 
v___x_1684_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1323_, v___x_1683_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1684_;
}
}
}
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
lean_dec(v_numParams_1579_);
lean_dec(v_cidx_1578_);
lean_del_object(v___x_1575_);
lean_dec(v_a_1484_);
lean_dec(v_declName_1479_);
lean_del_object(v___x_1345_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_decl_1322_);
v_a_1692_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1601_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1601_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
lean_dec(v_numParams_1579_);
lean_dec(v_cidx_1578_);
lean_dec(v_induct_1577_);
lean_del_object(v___x_1575_);
lean_dec(v_a_1484_);
lean_dec_ref(v_args_1480_);
lean_dec(v_declName_1479_);
lean_del_object(v___x_1345_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_decl_1322_);
v_a_1700_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1580_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1580_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
}
case 7:
{
lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1724_; 
lean_dec(v_a_1484_);
lean_dec_ref(v_args_1480_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_decl_1322_);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_val_1504_);
if (v_isSharedCheck_1724_ == 0)
{
lean_object* v_unused_1725_; 
v_unused_1725_ = lean_ctor_get(v_val_1504_, 0);
lean_dec(v_unused_1725_);
v___x_1710_ = v_val_1504_;
v_isShared_1711_ = v_isSharedCheck_1724_;
goto v_resetjp_1709_;
}
else
{
lean_dec(v_val_1504_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1724_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1712_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__11));
v___x_1713_ = l_Lean_Name_toString(v_declName_1479_, v___x_1348_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set_tag(v___x_1710_, 3);
lean_ctor_set(v___x_1710_, 0, v___x_1713_);
v___x_1715_ = v___x_1710_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
lean_object* v___x_1717_; 
if (v_isShared_1346_ == 0)
{
lean_ctor_set_tag(v___x_1345_, 5);
lean_ctor_set(v___x_1345_, 1, v___x_1715_);
lean_ctor_set(v___x_1345_, 0, v___x_1712_);
v___x_1717_ = v___x_1345_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1712_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1718_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___closed__13));
v___x_1719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1717_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
v___x_1720_ = l_Lean_MessageData_ofFormat(v___x_1719_);
v___x_1721_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_1720_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1721_;
}
}
}
}
default: 
{
lean_object* v___x_1726_; 
lean_dec(v_val_1504_);
lean_dec_ref(v_args_1480_);
lean_del_object(v___x_1345_);
v___x_1726_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_1322_, v_k_1323_, v_declName_1479_, v_a_1484_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1726_;
}
}
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec(v_a_1484_);
lean_dec_ref(v_args_1480_);
lean_dec(v_declName_1479_);
lean_del_object(v___x_1345_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_decl_1322_);
v_a_1727_ = lean_ctor_get(v___x_1491_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1491_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1491_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1491_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec(v_a_1484_);
lean_dec_ref(v_args_1480_);
lean_dec(v_declName_1479_);
lean_del_object(v___x_1345_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_decl_1322_);
v_a_1735_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1485_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1485_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
lean_dec_ref(v_args_1480_);
lean_dec(v_declName_1479_);
lean_del_object(v___x_1345_);
lean_dec_ref(v_k_1323_);
lean_dec_ref(v_decl_1322_);
v_a_1743_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1483_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1483_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
default: 
{
lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1790_; 
lean_inc_ref(v_type_1341_);
lean_inc(v_binderName_1340_);
lean_inc(v_fvarId_1339_);
lean_del_object(v___x_1345_);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_decl_1322_);
if (v_isSharedCheck_1790_ == 0)
{
lean_object* v_unused_1791_; lean_object* v_unused_1792_; lean_object* v_unused_1793_; lean_object* v_unused_1794_; 
v_unused_1791_ = lean_ctor_get(v_decl_1322_, 3);
lean_dec(v_unused_1791_);
v_unused_1792_ = lean_ctor_get(v_decl_1322_, 2);
lean_dec(v_unused_1792_);
v_unused_1793_ = lean_ctor_get(v_decl_1322_, 1);
lean_dec(v_unused_1793_);
v_unused_1794_ = lean_ctor_get(v_decl_1322_, 0);
lean_dec(v_unused_1794_);
v___x_1752_ = v_decl_1322_;
v_isShared_1753_ = v_isSharedCheck_1790_;
goto v_resetjp_1751_;
}
else
{
lean_dec(v_decl_1322_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1790_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v_fvarId_1754_; lean_object* v_args_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1789_; 
v_fvarId_1754_ = lean_ctor_get(v___x_1349_, 0);
v_args_1755_ = lean_ctor_get(v___x_1349_, 1);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1757_ = v___x_1349_;
v_isShared_1758_ = v_isSharedCheck_1789_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_args_1755_);
lean_inc(v_fvarId_1754_);
lean_dec(v___x_1349_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1789_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
size_t v_sz_1759_; size_t v___x_1760_; lean_object* v___x_1761_; 
v_sz_1759_ = lean_array_size(v_args_1755_);
v___x_1760_ = ((size_t)0ULL);
v___x_1761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_1759_, v___x_1760_, v_args_1755_, v_a_1324_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1763_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1761_, 1);
v___x_1763_ = l_Lean_Compiler_LCNF_toImpureType(v_type_1341_, v_a_1327_, v_a_1328_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1765_; lean_object* v___x_1767_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
v___x_1765_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_boxed(v_a_1764_);
lean_dec(v_a_1764_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 1, v_a_1762_);
v___x_1767_ = v___x_1757_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_fvarId_1754_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v___x_1769_; 
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 3, v___x_1767_);
lean_ctor_set(v___x_1752_, 2, v___x_1765_);
v___x_1769_ = v___x_1752_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_fvarId_1339_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_binderName_1340_);
lean_ctor_set(v_reuseFailAlloc_1771_, 2, v___x_1765_);
lean_ctor_set(v_reuseFailAlloc_1771_, 3, v___x_1767_);
v___x_1769_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v___x_1770_; 
v___x_1770_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_1323_, v___x_1769_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
return v___x_1770_;
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec(v_a_1762_);
lean_del_object(v___x_1757_);
lean_dec(v_fvarId_1754_);
lean_del_object(v___x_1752_);
lean_dec(v_binderName_1340_);
lean_dec(v_fvarId_1339_);
lean_dec_ref(v_k_1323_);
v_a_1773_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1763_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1763_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_del_object(v___x_1757_);
lean_dec(v_fvarId_1754_);
lean_del_object(v___x_1752_);
lean_dec_ref(v_type_1341_);
lean_dec(v_binderName_1340_);
lean_dec(v_fvarId_1339_);
lean_dec_ref(v_k_1323_);
v_a_1781_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1761_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1761_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
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
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1799_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__1));
v___x_1800_ = lean_unsigned_to_nat(15u);
v___x_1801_ = lean_unsigned_to_nat(272u);
v___x_1802_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1803_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1804_ = l_mkPanicMessageWithDecl(v___x_1803_, v___x_1802_, v___x_1801_, v___x_1800_, v___x_1799_);
return v___x_1804_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6(void){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1808_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__5));
v___x_1809_ = lean_unsigned_to_nat(6u);
v___x_1810_ = lean_unsigned_to_nat(251u);
v___x_1811_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1812_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1813_ = l_mkPanicMessageWithDecl(v___x_1812_, v___x_1811_, v___x_1810_, v___x_1809_, v___x_1808_);
return v___x_1813_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7(void){
_start:
{
uint8_t v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = 0;
v___x_1815_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v___x_1814_);
return v___x_1815_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9(void){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1817_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__8));
v___x_1818_ = lean_unsigned_to_nat(6u);
v___x_1819_ = lean_unsigned_to_nat(253u);
v___x_1820_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1821_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1822_ = l_mkPanicMessageWithDecl(v___x_1821_, v___x_1820_, v___x_1819_, v___x_1818_, v___x_1817_);
return v___x_1822_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11(void){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1824_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__10));
v___x_1825_ = lean_unsigned_to_nat(6u);
v___x_1826_ = lean_unsigned_to_nat(254u);
v___x_1827_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1828_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1829_ = l_mkPanicMessageWithDecl(v___x_1828_, v___x_1827_, v___x_1826_, v___x_1825_, v___x_1824_);
return v___x_1829_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13(void){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1831_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__12));
v___x_1832_ = lean_unsigned_to_nat(45u);
v___x_1833_ = lean_unsigned_to_nat(252u);
v___x_1834_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__0));
v___x_1835_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1836_ = l_mkPanicMessageWithDecl(v___x_1835_, v___x_1834_, v___x_1833_, v___x_1832_, v___x_1831_);
return v___x_1836_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2(void){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1839_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__1));
v___x_1840_ = lean_unsigned_to_nat(18u);
v___x_1841_ = lean_unsigned_to_nat(293u);
v___x_1842_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__0));
v___x_1843_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerResultType_resultTypeForArity___closed__0));
v___x_1844_ = l_mkPanicMessageWithDecl(v___x_1843_, v___x_1842_, v___x_1841_, v___x_1840_, v___x_1839_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(lean_object* v_discr_1845_, lean_object* v_k_1846_, lean_object* v_ctorInfo_1847_, lean_object* v_params_1848_, lean_object* v_fields_1849_, lean_object* v_i_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1927_; lean_object* v___x_1933_; uint8_t v___x_1934_; 
v___x_1933_ = lean_array_get_size(v_params_1848_);
v___x_1934_ = lean_nat_dec_lt(v_i_1850_, v___x_1933_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; 
v___x_1935_ = lean_box(0);
v___y_1927_ = v___x_1935_;
goto v___jp_1926_;
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = lean_array_fget_borrowed(v_params_1848_, v_i_1850_);
lean_inc(v___x_1936_);
v___x_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
v___y_1927_ = v___x_1937_;
goto v___jp_1926_;
}
v___jp_1857_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___closed__2);
v___x_1864_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_1863_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
return v___x_1864_;
}
v___jp_1865_:
{
if (lean_obj_tag(v___y_1866_) == 0)
{
lean_dec(v_i_1850_);
lean_dec(v_discr_1845_);
if (lean_obj_tag(v___y_1867_) == 0)
{
lean_object* v___x_1868_; 
v___x_1868_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_1846_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
return v___x_1868_;
}
else
{
lean_dec(v___y_1867_);
lean_dec_ref(v_k_1846_);
v___y_1858_ = v_a_1851_;
v___y_1859_ = v_a_1852_;
v___y_1860_ = v_a_1853_;
v___y_1861_ = v_a_1854_;
v___y_1862_ = v_a_1855_;
goto v___jp_1857_;
}
}
else
{
if (lean_obj_tag(v___y_1867_) == 1)
{
lean_object* v_val_1869_; lean_object* v_val_1870_; lean_object* v___x_1871_; lean_object* v_fst_1872_; 
v_val_1869_ = lean_ctor_get(v___y_1866_, 0);
lean_inc(v_val_1869_);
lean_dec_ref_known(v___y_1866_, 1);
v_val_1870_ = lean_ctor_get(v___y_1867_, 0);
lean_inc(v_val_1870_);
lean_dec_ref_known(v___y_1867_, 1);
lean_inc(v_discr_1845_);
v___x_1871_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerProj(v_discr_1845_, v_ctorInfo_1847_, v_val_1870_);
v_fst_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_fst_1872_);
if (lean_obj_tag(v_fst_1872_) == 1)
{
lean_object* v___x_1873_; lean_object* v_fvarId_1874_; lean_object* v_subst_1875_; lean_object* v_jpParamMask_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1889_; 
lean_dec_ref(v___x_1871_);
v___x_1873_ = lean_st_ref_take(v_a_1851_);
v_fvarId_1874_ = lean_ctor_get(v_val_1869_, 0);
lean_inc(v_fvarId_1874_);
lean_dec(v_val_1869_);
v_subst_1875_ = lean_ctor_get(v___x_1873_, 0);
v_jpParamMask_1876_ = lean_ctor_get(v___x_1873_, 1);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1878_ = v___x_1873_;
v_isShared_1879_ = v_isSharedCheck_1889_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_jpParamMask_1876_);
lean_inc(v_subst_1875_);
lean_dec(v___x_1873_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1889_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1880_ = lean_box(0);
v___x_1881_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_subst_1875_, v_fvarId_1874_, v___x_1880_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v___x_1881_);
v___x_1883_ = v___x_1878_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_jpParamMask_1876_);
v___x_1883_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = lean_st_ref_put(v_a_1851_, v___x_1883_);
v___x_1885_ = lean_unsigned_to_nat(1u);
v___x_1886_ = lean_nat_add(v_i_1850_, v___x_1885_);
lean_dec(v_i_1850_);
v_i_1850_ = v___x_1886_;
goto _start;
}
}
}
else
{
lean_object* v_snd_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1924_; 
v_snd_1890_ = lean_ctor_get(v___x_1871_, 1);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1924_ == 0)
{
lean_object* v_unused_1925_; 
v_unused_1925_ = lean_ctor_get(v___x_1871_, 0);
lean_dec(v_unused_1925_);
v___x_1892_ = v___x_1871_;
v_isShared_1893_ = v_isSharedCheck_1924_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_snd_1890_);
lean_dec(v___x_1871_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1924_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; lean_object* v_fvarId_1895_; lean_object* v_binderName_1896_; lean_object* v_lctx_1897_; lean_object* v_nextIdx_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1923_; 
v___x_1894_ = lean_st_ref_take(v_a_1853_);
v_fvarId_1895_ = lean_ctor_get(v_val_1869_, 0);
lean_inc(v_fvarId_1895_);
v_binderName_1896_ = lean_ctor_get(v_val_1869_, 1);
lean_inc(v_binderName_1896_);
lean_dec(v_val_1869_);
v_lctx_1897_ = lean_ctor_get(v___x_1894_, 0);
v_nextIdx_1898_ = lean_ctor_get(v___x_1894_, 1);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1900_ = v___x_1894_;
v_isShared_1901_ = v_isSharedCheck_1923_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_nextIdx_1898_);
lean_inc(v_lctx_1897_);
lean_dec(v___x_1894_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1923_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
uint8_t v___x_1902_; lean_object* v_decl_1903_; lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1902_ = 1;
v_decl_1903_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_decl_1903_, 0, v_fvarId_1895_);
lean_ctor_set(v_decl_1903_, 1, v_binderName_1896_);
lean_ctor_set(v_decl_1903_, 2, v_snd_1890_);
lean_ctor_set(v_decl_1903_, 3, v_fst_1872_);
lean_inc_ref(v_decl_1903_);
v___x_1904_ = l_Lean_Compiler_LCNF_LCtx_addLetDecl(v___x_1902_, v_lctx_1897_, v_decl_1903_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 0, v___x_1904_);
v___x_1906_ = v___x_1900_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1904_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_nextIdx_1898_);
v___x_1906_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1907_ = lean_st_ref_put(v_a_1853_, v___x_1906_);
v___x_1908_ = lean_unsigned_to_nat(1u);
v___x_1909_ = lean_nat_add(v_i_1850_, v___x_1908_);
lean_dec(v_i_1850_);
v___x_1910_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_1845_, v_k_1846_, v_ctorInfo_1847_, v_params_1848_, v_fields_1849_, v___x_1909_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1921_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1913_ = v___x_1910_;
v_isShared_1914_ = v_isSharedCheck_1921_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1921_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 1, v_a_1911_);
lean_ctor_set(v___x_1892_, 0, v_decl_1903_);
v___x_1916_ = v___x_1892_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_decl_1903_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1918_; 
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 0, v___x_1916_);
v___x_1918_ = v___x_1913_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
else
{
lean_dec_ref_known(v_decl_1903_, 4);
lean_del_object(v___x_1892_);
return v___x_1910_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v___y_1866_, 1);
lean_dec(v___y_1867_);
lean_dec(v_i_1850_);
lean_dec_ref(v_k_1846_);
lean_dec(v_discr_1845_);
v___y_1858_ = v_a_1851_;
v___y_1859_ = v_a_1852_;
v___y_1860_ = v_a_1853_;
v___y_1861_ = v_a_1854_;
v___y_1862_ = v_a_1855_;
goto v___jp_1857_;
}
}
}
v___jp_1926_:
{
lean_object* v___x_1928_; uint8_t v___x_1929_; 
v___x_1928_ = lean_array_get_size(v_fields_1849_);
v___x_1929_ = lean_nat_dec_lt(v_i_1850_, v___x_1928_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; 
v___x_1930_ = lean_box(0);
v___y_1866_ = v___y_1927_;
v___y_1867_ = v___x_1930_;
goto v___jp_1865_;
}
else
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = lean_array_fget_borrowed(v_fields_1849_, v_i_1850_);
lean_inc(v___x_1931_);
v___x_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
v___y_1866_ = v___y_1927_;
v___y_1867_ = v___x_1932_;
goto v___jp_1865_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(lean_object* v_discr_1938_, lean_object* v_alt_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
if (lean_obj_tag(v_alt_1939_) == 0)
{
lean_object* v_ctorName_1946_; lean_object* v_params_1947_; lean_object* v_code_1948_; lean_object* v___x_1949_; 
v_ctorName_1946_ = lean_ctor_get(v_alt_1939_, 0);
lean_inc(v_ctorName_1946_);
v_params_1947_ = lean_ctor_get(v_alt_1939_, 1);
lean_inc_ref(v_params_1947_);
v_code_1948_ = lean_ctor_get(v_alt_1939_, 2);
lean_inc_ref(v_code_1948_);
lean_dec_ref_known(v_alt_1939_, 3);
v___x_1949_ = l_Lean_Compiler_LCNF_getCtorLayout(v_ctorName_1946_, v_a_1943_, v_a_1944_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; lean_object* v_ctorInfo_1951_; lean_object* v_fieldInfo_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1977_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref_known(v___x_1949_, 1);
v_ctorInfo_1951_ = lean_ctor_get(v_a_1950_, 0);
v_fieldInfo_1952_ = lean_ctor_get(v_a_1950_, 1);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_a_1950_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1954_ = v_a_1950_;
v_isShared_1955_ = v_isSharedCheck_1977_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_fieldInfo_1952_);
lean_inc(v_ctorInfo_1951_);
lean_dec(v_a_1950_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1977_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = lean_unsigned_to_nat(0u);
v___x_1957_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_1938_, v_code_1948_, v_ctorInfo_1951_, v_params_1947_, v_fieldInfo_1952_, v___x_1956_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
lean_dec_ref(v_fieldInfo_1952_);
lean_dec_ref(v_params_1947_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1968_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1960_ = v___x_1957_;
v_isShared_1961_ = v_isSharedCheck_1968_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1957_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1968_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1955_ == 0)
{
lean_ctor_set_tag(v___x_1954_, 1);
lean_ctor_set(v___x_1954_, 1, v_a_1958_);
v___x_1963_ = v___x_1954_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_ctorInfo_1951_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
lean_object* v___x_1965_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v___x_1963_);
v___x_1965_ = v___x_1960_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
else
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1976_; 
lean_del_object(v___x_1954_);
lean_dec_ref(v_ctorInfo_1951_);
v_a_1969_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1971_ = v___x_1957_;
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1957_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1976_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1969_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
lean_dec_ref(v_code_1948_);
lean_dec_ref(v_params_1947_);
lean_dec(v_discr_1938_);
v_a_1978_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1949_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1949_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
else
{
lean_object* v_code_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2010_; 
lean_dec(v_discr_1938_);
v_code_1986_ = lean_ctor_get(v_alt_1939_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_alt_1939_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1988_ = v_alt_1939_;
v_isShared_1989_ = v_isSharedCheck_2010_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_code_1986_);
lean_dec(v_alt_1939_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2010_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1990_; 
v___x_1990_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_code_1986_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2001_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1993_ = v___x_1990_;
v_isShared_1994_ = v_isSharedCheck_2001_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2001_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v_a_1991_);
v___x_1996_ = v___x_1988_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1998_; 
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_1996_);
v___x_1998_ = v___x_1993_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
lean_del_object(v___x_1988_);
v_a_2002_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1990_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1990_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(lean_object* v_fvarId_2011_, size_t v_sz_2012_, size_t v_i_2013_, lean_object* v_bs_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
uint8_t v___x_2021_; 
v___x_2021_ = lean_usize_dec_lt(v_i_2013_, v_sz_2012_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; 
lean_dec(v_fvarId_2011_);
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v_bs_2014_);
return v___x_2022_;
}
else
{
lean_object* v_v_2023_; lean_object* v___x_2024_; 
v_v_2023_ = lean_array_uget_borrowed(v_bs_2014_, v_i_2013_);
lean_inc(v_v_2023_);
lean_inc(v_fvarId_2011_);
v___x_2024_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(v_fvarId_2011_, v_v_2023_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2026_; lean_object* v_bs_x27_2027_; size_t v___x_2028_; size_t v___x_2029_; lean_object* v___x_2030_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2024_, 1);
v___x_2026_ = lean_unsigned_to_nat(0u);
v_bs_x27_2027_ = lean_array_uset(v_bs_2014_, v_i_2013_, v___x_2026_);
v___x_2028_ = ((size_t)1ULL);
v___x_2029_ = lean_usize_add(v_i_2013_, v___x_2028_);
v___x_2030_ = lean_array_uset(v_bs_x27_2027_, v_i_2013_, v_a_2025_);
v_i_2013_ = v___x_2029_;
v_bs_2014_ = v___x_2030_;
goto _start;
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec_ref(v_bs_2014_);
lean_dec(v_fvarId_2011_);
v_a_2032_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2024_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2024_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(lean_object* v_c_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_){
_start:
{
switch(lean_obj_tag(v_c_2040_))
{
case 0:
{
lean_object* v_decl_2047_; lean_object* v_k_2048_; lean_object* v___x_2049_; 
v_decl_2047_ = lean_ctor_get(v_c_2040_, 0);
lean_inc_ref(v_decl_2047_);
v_k_2048_ = lean_ctor_get(v_c_2040_, 1);
lean_inc_ref(v_k_2048_);
lean_dec_ref_known(v_c_2040_, 2);
v___x_2049_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(v_decl_2047_, v_k_2048_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
return v___x_2049_;
}
case 1:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
lean_dec_ref_known(v_c_2040_, 2);
v___x_2050_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__2);
v___x_2051_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2050_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
return v___x_2051_;
}
case 2:
{
lean_object* v_decl_2052_; lean_object* v_k_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2145_; 
v_decl_2052_ = lean_ctor_get(v_c_2040_, 0);
v_k_2053_ = lean_ctor_get(v_c_2040_, 1);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_c_2040_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2055_ = v_c_2040_;
v_isShared_2056_ = v_isSharedCheck_2145_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_k_2053_);
lean_inc(v_decl_2052_);
lean_dec(v_c_2040_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2145_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v_fvarId_2057_; lean_object* v_binderName_2058_; lean_object* v_params_2059_; lean_object* v_type_2060_; lean_object* v_value_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2144_; 
v_fvarId_2057_ = lean_ctor_get(v_decl_2052_, 0);
v_binderName_2058_ = lean_ctor_get(v_decl_2052_, 1);
v_params_2059_ = lean_ctor_get(v_decl_2052_, 2);
v_type_2060_ = lean_ctor_get(v_decl_2052_, 3);
v_value_2061_ = lean_ctor_get(v_decl_2052_, 4);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_decl_2052_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2063_ = v_decl_2052_;
v_isShared_2064_ = v_isSharedCheck_2144_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_value_2061_);
lean_inc(v_type_2060_);
lean_inc(v_params_2059_);
lean_inc(v_binderName_2058_);
lean_inc(v_fvarId_2057_);
lean_dec(v_decl_2052_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2144_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
size_t v_sz_2065_; size_t v___x_2066_; lean_object* v___x_2067_; 
v_sz_2065_ = lean_array_size(v_params_2059_);
v___x_2066_ = ((size_t)0ULL);
v___x_2067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2065_, v___x_2066_, v_params_2059_, v_a_2041_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; lean_object* v___x_2069_; lean_object* v_subst_2070_; lean_object* v_jpParamMask_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2135_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
lean_dec_ref_known(v___x_2067_, 1);
v___x_2069_ = lean_st_ref_take(v_a_2041_);
v_subst_2070_ = lean_ctor_get(v___x_2069_, 0);
v_jpParamMask_2071_ = lean_ctor_get(v___x_2069_, 1);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2073_ = v___x_2069_;
v_isShared_2074_ = v_isSharedCheck_2135_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_jpParamMask_2071_);
lean_inc(v_subst_2070_);
lean_dec(v___x_2069_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2135_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
size_t v_sz_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2079_; 
v_sz_2075_ = lean_array_size(v_a_2068_);
lean_inc(v_a_2068_);
v___x_2076_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__3(v_sz_2075_, v___x_2066_, v_a_2068_);
lean_inc_ref(v___x_2076_);
lean_inc(v_fvarId_2057_);
v___x_2077_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Param_toImpure_spec__0___redArg(v_jpParamMask_2071_, v_fvarId_2057_, v___x_2076_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 1, v___x_2077_);
v___x_2079_ = v___x_2073_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_subst_2070_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v___x_2077_);
v___x_2079_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2080_; lean_object* v___y_2082_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; uint8_t v___x_2128_; 
v___x_2080_ = lean_st_ref_put(v_a_2041_, v___x_2079_);
v___x_2124_ = lean_unsigned_to_nat(0u);
v___x_2125_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__3));
v___x_2126_ = l_Array_zip___redArg(v_a_2068_, v___x_2076_);
lean_dec_ref(v___x_2076_);
v___x_2127_ = lean_array_get_size(v___x_2126_);
v___x_2128_ = lean_nat_dec_lt(v___x_2124_, v___x_2127_);
if (v___x_2128_ == 0)
{
lean_dec_ref(v___x_2126_);
v___y_2082_ = v___x_2125_;
goto v___jp_2081_;
}
else
{
uint8_t v___x_2129_; 
v___x_2129_ = lean_nat_dec_le(v___x_2127_, v___x_2127_);
if (v___x_2129_ == 0)
{
if (v___x_2128_ == 0)
{
lean_dec_ref(v___x_2126_);
v___y_2082_ = v___x_2125_;
goto v___jp_2081_;
}
else
{
size_t v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = lean_usize_of_nat(v___x_2127_);
v___x_2131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v___x_2126_, v___x_2066_, v___x_2130_, v___x_2125_);
lean_dec_ref(v___x_2126_);
v___y_2082_ = v___x_2131_;
goto v___jp_2081_;
}
}
else
{
size_t v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = lean_usize_of_nat(v___x_2127_);
v___x_2133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__4(v___x_2126_, v___x_2066_, v___x_2132_, v___x_2125_);
lean_dec_ref(v___x_2126_);
v___y_2082_ = v___x_2133_;
goto v___jp_2081_;
}
}
v___jp_2081_:
{
lean_object* v___x_2083_; 
v___x_2083_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_value_2061_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v___x_2085_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2084_);
lean_dec_ref_known(v___x_2083_, 1);
v___x_2085_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_2053_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2085_, 1);
v___x_2087_ = lean_array_get_size(v_a_2068_);
lean_dec(v_a_2068_);
v___x_2088_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_2060_, v___x_2087_, v_a_2044_, v_a_2045_);
lean_dec_ref(v_type_2060_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2115_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2091_ = v___x_2088_;
v_isShared_2092_ = v_isSharedCheck_2115_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2115_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; lean_object* v_lctx_2094_; lean_object* v_nextIdx_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2114_; 
v___x_2093_ = lean_st_ref_take(v_a_2043_);
v_lctx_2094_ = lean_ctor_get(v___x_2093_, 0);
v_nextIdx_2095_ = lean_ctor_get(v___x_2093_, 1);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2097_ = v___x_2093_;
v_isShared_2098_ = v_isSharedCheck_2114_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_nextIdx_2095_);
lean_inc(v_lctx_2094_);
lean_dec(v___x_2093_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2114_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
uint8_t v___x_2099_; lean_object* v___x_2101_; 
v___x_2099_ = 1;
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 4, v_a_2084_);
lean_ctor_set(v___x_2063_, 3, v_a_2089_);
lean_ctor_set(v___x_2063_, 2, v___y_2082_);
v___x_2101_ = v___x_2063_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_fvarId_2057_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_binderName_2058_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v___y_2082_);
lean_ctor_set(v_reuseFailAlloc_2113_, 3, v_a_2089_);
lean_ctor_set(v_reuseFailAlloc_2113_, 4, v_a_2084_);
v___x_2101_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2102_; lean_object* v___x_2104_; 
lean_inc_ref(v___x_2101_);
v___x_2102_ = l_Lean_Compiler_LCNF_LCtx_addFunDecl(v___x_2099_, v_lctx_2094_, v___x_2101_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2102_);
v___x_2104_ = v___x_2097_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2102_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_nextIdx_2095_);
v___x_2104_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2105_ = lean_st_ref_put(v_a_2043_, v___x_2104_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 1, v_a_2086_);
lean_ctor_set(v___x_2055_, 0, v___x_2101_);
v___x_2107_ = v___x_2055_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2101_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v_a_2086_);
v___x_2107_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2109_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2107_);
v___x_2109_ = v___x_2091_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec(v_a_2086_);
lean_dec(v_a_2084_);
lean_dec_ref(v___y_2082_);
lean_del_object(v___x_2063_);
lean_dec(v_binderName_2058_);
lean_dec(v_fvarId_2057_);
lean_del_object(v___x_2055_);
v_a_2116_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2088_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2088_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
else
{
lean_dec(v_a_2084_);
lean_dec_ref(v___y_2082_);
lean_dec(v_a_2068_);
lean_del_object(v___x_2063_);
lean_dec_ref(v_type_2060_);
lean_dec(v_binderName_2058_);
lean_dec(v_fvarId_2057_);
lean_del_object(v___x_2055_);
return v___x_2085_;
}
}
else
{
lean_dec_ref(v___y_2082_);
lean_dec(v_a_2068_);
lean_del_object(v___x_2063_);
lean_dec_ref(v_type_2060_);
lean_dec(v_binderName_2058_);
lean_dec(v_fvarId_2057_);
lean_del_object(v___x_2055_);
lean_dec_ref(v_k_2053_);
return v___x_2083_;
}
}
}
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_del_object(v___x_2063_);
lean_dec_ref(v_value_2061_);
lean_dec_ref(v_type_2060_);
lean_dec(v_binderName_2058_);
lean_dec(v_fvarId_2057_);
lean_del_object(v___x_2055_);
lean_dec_ref(v_k_2053_);
v_a_2136_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2067_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2067_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
}
}
case 3:
{
lean_object* v_fvarId_2146_; lean_object* v_args_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2183_; 
v_fvarId_2146_ = lean_ctor_get(v_c_2040_, 0);
v_args_2147_ = lean_ctor_get(v_c_2040_, 1);
v_isSharedCheck_2183_ = !lean_is_exclusive(v_c_2040_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2149_ = v_c_2040_;
v_isShared_2150_ = v_isSharedCheck_2183_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_args_2147_);
lean_inc(v_fvarId_2146_);
lean_dec(v_c_2040_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2183_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v_a_2152_; lean_object* v___y_2158_; lean_object* v___x_2168_; lean_object* v_jpParamMask_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2168_ = lean_st_ref_get(v_a_2041_);
v_jpParamMask_2169_ = lean_ctor_get(v___x_2168_, 1);
lean_inc_ref(v_jpParamMask_2169_);
lean_dec(v___x_2168_);
v___x_2170_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__5(v_jpParamMask_2169_, v_fvarId_2146_);
lean_dec_ref(v_jpParamMask_2169_);
v___x_2171_ = lean_unsigned_to_nat(0u);
v___x_2172_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__4));
v___x_2173_ = l_Array_zip___redArg(v_args_2147_, v___x_2170_);
lean_dec_ref(v___x_2170_);
lean_dec_ref(v_args_2147_);
v___x_2174_ = lean_array_get_size(v___x_2173_);
v___x_2175_ = lean_nat_dec_lt(v___x_2171_, v___x_2174_);
if (v___x_2175_ == 0)
{
lean_dec_ref(v___x_2173_);
v_a_2152_ = v___x_2172_;
goto v___jp_2151_;
}
else
{
uint8_t v___x_2176_; 
v___x_2176_ = lean_nat_dec_le(v___x_2174_, v___x_2174_);
if (v___x_2176_ == 0)
{
if (v___x_2175_ == 0)
{
lean_dec_ref(v___x_2173_);
v_a_2152_ = v___x_2172_;
goto v___jp_2151_;
}
else
{
size_t v___x_2177_; size_t v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = ((size_t)0ULL);
v___x_2178_ = lean_usize_of_nat(v___x_2174_);
v___x_2179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v___x_2173_, v___x_2177_, v___x_2178_, v___x_2172_, v_a_2041_);
lean_dec_ref(v___x_2173_);
v___y_2158_ = v___x_2179_;
goto v___jp_2157_;
}
}
else
{
size_t v___x_2180_; size_t v___x_2181_; lean_object* v___x_2182_; 
v___x_2180_ = ((size_t)0ULL);
v___x_2181_ = lean_usize_of_nat(v___x_2174_);
v___x_2182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v___x_2173_, v___x_2180_, v___x_2181_, v___x_2172_, v_a_2041_);
lean_dec_ref(v___x_2173_);
v___y_2158_ = v___x_2182_;
goto v___jp_2157_;
}
}
v___jp_2151_:
{
lean_object* v___x_2154_; 
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 1, v_a_2152_);
v___x_2154_ = v___x_2149_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_fvarId_2146_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_a_2152_);
v___x_2154_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; 
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
return v___x_2155_;
}
}
v___jp_2157_:
{
if (lean_obj_tag(v___y_2158_) == 0)
{
lean_object* v_a_2159_; 
v_a_2159_ = lean_ctor_get(v___y_2158_, 0);
lean_inc(v_a_2159_);
lean_dec_ref_known(v___y_2158_, 1);
v_a_2152_ = v_a_2159_;
goto v___jp_2151_;
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_del_object(v___x_2149_);
lean_dec(v_fvarId_2146_);
v_a_2160_ = lean_ctor_get(v___y_2158_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___y_2158_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___y_2158_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___y_2158_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
}
case 4:
{
lean_object* v_cases_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2294_; 
v_cases_2184_ = lean_ctor_get(v_c_2040_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v_c_2040_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2186_ = v_c_2040_;
v_isShared_2187_ = v_isSharedCheck_2294_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_cases_2184_);
lean_dec(v_c_2040_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2294_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v_typeName_2188_; lean_object* v_resultType_2189_; lean_object* v_discr_2190_; lean_object* v_alts_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2293_; 
v_typeName_2188_ = lean_ctor_get(v_cases_2184_, 0);
v_resultType_2189_ = lean_ctor_get(v_cases_2184_, 1);
v_discr_2190_ = lean_ctor_get(v_cases_2184_, 2);
v_alts_2191_ = lean_ctor_get(v_cases_2184_, 3);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_cases_2184_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2193_ = v_cases_2184_;
v_isShared_2194_ = v_isSharedCheck_2293_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_alts_2191_);
lean_inc(v_discr_2190_);
lean_inc(v_resultType_2189_);
lean_inc(v_typeName_2188_);
lean_dec(v_cases_2184_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2293_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; 
lean_inc(v_typeName_2188_);
v___x_2195_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_typeName_2188_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref_known(v___x_2195_, 1);
if (lean_obj_tag(v_a_2196_) == 1)
{
lean_object* v_val_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; 
lean_del_object(v___x_2193_);
lean_dec_ref(v_resultType_2189_);
lean_dec(v_typeName_2188_);
lean_del_object(v___x_2186_);
v_val_2197_ = lean_ctor_get(v_a_2196_, 0);
lean_inc(v_val_2197_);
lean_dec_ref_known(v_a_2196_, 1);
v___x_2198_ = lean_array_get_size(v_alts_2191_);
v___x_2199_ = lean_unsigned_to_nat(1u);
v___x_2200_ = lean_nat_dec_eq(v___x_2198_, v___x_2199_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_dec(v_val_2197_);
lean_dec_ref(v_alts_2191_);
lean_dec(v_discr_2190_);
v___x_2201_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__6);
v___x_2202_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2201_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
return v___x_2202_;
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__7);
v___x_2204_ = lean_unsigned_to_nat(0u);
v___x_2205_ = lean_array_get(v___x_2203_, v_alts_2191_, v___x_2204_);
lean_dec_ref(v_alts_2191_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_ctorName_2206_; lean_object* v_params_2207_; lean_object* v_code_2208_; lean_object* v_ctorName_2209_; lean_object* v_fieldIdx_2210_; uint8_t v___x_2211_; 
v_ctorName_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_ctorName_2206_);
v_params_2207_ = lean_ctor_get(v___x_2205_, 1);
lean_inc_ref(v_params_2207_);
v_code_2208_ = lean_ctor_get(v___x_2205_, 2);
lean_inc_ref(v_code_2208_);
lean_dec_ref_known(v___x_2205_, 3);
v_ctorName_2209_ = lean_ctor_get(v_val_2197_, 0);
lean_inc(v_ctorName_2209_);
v_fieldIdx_2210_ = lean_ctor_get(v_val_2197_, 2);
lean_inc(v_fieldIdx_2210_);
lean_dec(v_val_2197_);
v___x_2211_ = lean_name_eq(v_ctorName_2206_, v_ctorName_2209_);
lean_dec(v_ctorName_2209_);
lean_dec(v_ctorName_2206_);
if (v___x_2211_ == 0)
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_dec(v_fieldIdx_2210_);
lean_dec_ref(v_code_2208_);
lean_dec_ref(v_params_2207_);
lean_dec(v_discr_2190_);
v___x_2212_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__9);
v___x_2213_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2212_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
return v___x_2213_;
}
else
{
lean_object* v___x_2214_; uint8_t v___x_2215_; 
v___x_2214_ = lean_array_get_size(v_params_2207_);
v___x_2215_ = lean_nat_dec_lt(v_fieldIdx_2210_, v___x_2214_);
if (v___x_2215_ == 0)
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
lean_dec(v_fieldIdx_2210_);
lean_dec_ref(v_code_2208_);
lean_dec_ref(v_params_2207_);
lean_dec(v_discr_2190_);
v___x_2216_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__11);
v___x_2217_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2216_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
return v___x_2217_;
}
else
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = lean_box(0);
v___x_2219_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v___x_2214_, v_params_2207_, v_fieldIdx_2210_, v_discr_2190_, v___x_2204_, v___x_2218_, v_a_2041_);
lean_dec(v_fieldIdx_2210_);
lean_dec_ref(v_params_2207_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_dec_ref_known(v___x_2219_, 1);
v_c_2040_ = v_code_2208_;
goto _start;
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_dec_ref(v_code_2208_);
v_a_2221_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2219_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2219_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
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
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
lean_dec(v___x_2205_);
lean_dec(v_val_2197_);
lean_dec(v_discr_2190_);
v___x_2229_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___closed__13);
v___x_2230_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop_spec__0(v___x_2229_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
return v___x_2230_;
}
}
}
else
{
lean_object* v___x_2231_; lean_object* v_subst_2232_; uint8_t v___x_2233_; lean_object* v___x_2234_; 
lean_dec(v_a_2196_);
v___x_2231_ = lean_st_ref_get(v_a_2041_);
v_subst_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc_ref(v_subst_2232_);
lean_dec(v___x_2231_);
v___x_2233_ = 1;
v___x_2234_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_2232_, v_discr_2190_, v___x_2233_);
lean_dec_ref(v_subst_2232_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_fvarId_2235_; lean_object* v___x_2236_; 
v_fvarId_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_fvarId_2235_);
lean_dec_ref_known(v___x_2234_, 1);
v___x_2236_ = l_Lean_Compiler_LCNF_toImpureType(v_resultType_2189_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; size_t v_sz_2238_; size_t v___x_2239_; lean_object* v___x_2240_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2237_);
lean_dec_ref_known(v___x_2236_, 1);
v_sz_2238_ = lean_array_size(v_alts_2191_);
v___x_2239_ = ((size_t)0ULL);
lean_inc(v_fvarId_2235_);
v___x_2240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(v_fvarId_2235_, v_sz_2238_, v___x_2239_, v_alts_2191_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2242_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2241_);
lean_dec_ref_known(v___x_2240_, 1);
v___x_2242_ = l_Lean_Compiler_LCNF_nameToImpureType(v_typeName_2188_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2258_; 
v_a_2243_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2245_ = v___x_2242_;
v_isShared_2246_ = v_isSharedCheck_2258_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2242_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2258_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2250_; 
v___x_2247_ = l_Lean_Expr_getAppFn(v_a_2243_);
lean_dec(v_a_2243_);
v___x_2248_ = l_Lean_Expr_constName_x21(v___x_2247_);
lean_dec_ref(v___x_2247_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 3, v_a_2241_);
lean_ctor_set(v___x_2193_, 2, v_fvarId_2235_);
lean_ctor_set(v___x_2193_, 1, v_a_2237_);
lean_ctor_set(v___x_2193_, 0, v___x_2248_);
v___x_2250_ = v___x_2193_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2248_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_a_2237_);
lean_ctor_set(v_reuseFailAlloc_2257_, 2, v_fvarId_2235_);
lean_ctor_set(v_reuseFailAlloc_2257_, 3, v_a_2241_);
v___x_2250_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
lean_object* v___x_2252_; 
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v___x_2250_);
v___x_2252_ = v___x_2186_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2250_);
v___x_2252_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
lean_object* v___x_2254_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v___x_2252_);
v___x_2254_ = v___x_2245_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2252_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_dec(v_a_2241_);
lean_dec(v_a_2237_);
lean_dec(v_fvarId_2235_);
lean_del_object(v___x_2193_);
lean_del_object(v___x_2186_);
v_a_2259_ = lean_ctor_get(v___x_2242_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2242_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2242_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2242_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_dec(v_a_2237_);
lean_dec(v_fvarId_2235_);
lean_del_object(v___x_2193_);
lean_dec(v_typeName_2188_);
lean_del_object(v___x_2186_);
v_a_2267_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2240_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2240_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
else
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
lean_dec(v_fvarId_2235_);
lean_del_object(v___x_2193_);
lean_dec_ref(v_alts_2191_);
lean_dec(v_typeName_2188_);
lean_del_object(v___x_2186_);
v_a_2275_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2236_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2236_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
else
{
uint8_t v___x_2283_; lean_object* v___x_2284_; 
lean_del_object(v___x_2193_);
lean_dec_ref(v_alts_2191_);
lean_dec_ref(v_resultType_2189_);
lean_dec(v_typeName_2188_);
lean_del_object(v___x_2186_);
v___x_2283_ = 1;
v___x_2284_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_2283_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
return v___x_2284_;
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_del_object(v___x_2193_);
lean_dec_ref(v_alts_2191_);
lean_dec(v_discr_2190_);
lean_dec_ref(v_resultType_2189_);
lean_dec(v_typeName_2188_);
lean_del_object(v___x_2186_);
v_a_2285_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2195_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2195_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
}
}
case 5:
{
lean_object* v_fvarId_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2316_; 
v_fvarId_2295_ = lean_ctor_get(v_c_2040_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_c_2040_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2297_ = v_c_2040_;
v_isShared_2298_ = v_isSharedCheck_2316_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_fvarId_2295_);
lean_dec(v_c_2040_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2316_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2299_; lean_object* v_subst_2300_; uint8_t v___x_2301_; lean_object* v___x_2302_; 
v___x_2299_ = lean_st_ref_get(v_a_2041_);
v_subst_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc_ref(v_subst_2300_);
lean_dec(v___x_2299_);
v___x_2301_ = 1;
v___x_2302_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(v_subst_2300_, v_fvarId_2295_, v___x_2301_);
lean_dec_ref(v_subst_2300_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_fvarId_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2313_; 
v_fvarId_2303_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2305_ = v___x_2302_;
v_isShared_2306_ = v_isSharedCheck_2313_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_fvarId_2303_);
lean_dec(v___x_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2313_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v_fvarId_2303_);
v___x_2308_ = v___x_2297_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_fvarId_2303_);
v___x_2308_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2310_; 
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v___x_2308_);
v___x_2310_ = v___x_2305_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2308_);
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
else
{
uint8_t v___x_2314_; lean_object* v___x_2315_; 
lean_del_object(v___x_2297_);
v___x_2314_ = 1;
v___x_2315_ = l_Lean_Compiler_LCNF_mkReturnErased(v___x_2314_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
return v___x_2315_;
}
}
}
default: 
{
lean_object* v_type_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2341_; 
v_type_2317_ = lean_ctor_get(v_c_2040_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_c_2040_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2319_ = v_c_2040_;
v_isShared_2320_ = v_isSharedCheck_2341_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_type_2317_);
lean_dec(v_c_2040_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2341_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Lean_Compiler_LCNF_toImpureType(v_type_2317_, v_a_2044_, v_a_2045_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2332_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2324_ = v___x_2321_;
v_isShared_2325_ = v_isSharedCheck_2332_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2321_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2332_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v_a_2322_);
v___x_2327_ = v___x_2319_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2329_; 
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 0, v___x_2327_);
v___x_2329_ = v___x_2324_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_del_object(v___x_2319_);
v_a_2333_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2321_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2321_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(lean_object* v_decl_2342_, lean_object* v_k_2343_, lean_object* v_ctorInfo_2344_, lean_object* v_fields_2345_, lean_object* v_irArgs_2346_, lean_object* v_i_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v___x_2354_; uint8_t v___x_2355_; 
v___x_2354_ = lean_array_get_size(v_irArgs_2346_);
v___x_2355_ = lean_nat_dec_lt(v_i_2347_, v___x_2354_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; 
lean_dec(v_i_2347_);
lean_dec_ref(v_decl_2342_);
v___x_2356_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_k_2343_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
return v___x_2356_;
}
else
{
lean_object* v___x_2357_; 
v___x_2357_ = lean_array_fget_borrowed(v_irArgs_2346_, v_i_2347_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = lean_unsigned_to_nat(1u);
v___x_2359_ = lean_nat_add(v_i_2347_, v___x_2358_);
lean_dec(v_i_2347_);
v_i_2347_ = v___x_2359_;
goto _start;
}
else
{
lean_object* v_fvarId_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v_fvarId_2361_ = lean_ctor_get(v___x_2357_, 0);
v___x_2362_ = lean_box(0);
v___x_2363_ = lean_array_get_borrowed(v___x_2362_, v_fields_2345_, v_i_2347_);
switch(lean_obj_tag(v___x_2363_))
{
case 1:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = lean_unsigned_to_nat(1u);
v___x_2365_ = lean_nat_add(v_i_2347_, v___x_2364_);
lean_dec(v_i_2347_);
v_i_2347_ = v___x_2365_;
goto _start;
}
case 2:
{
lean_object* v_i_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v_i_2367_ = lean_ctor_get(v___x_2363_, 0);
v___x_2368_ = lean_unsigned_to_nat(1u);
v___x_2369_ = lean_nat_add(v_i_2347_, v___x_2368_);
lean_dec(v_i_2347_);
lean_inc_ref(v_decl_2342_);
v___x_2370_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2342_, v_k_2343_, v_ctorInfo_2344_, v_fields_2345_, v_irArgs_2346_, v___x_2369_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2389_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2373_ = v___x_2370_;
v_isShared_2374_ = v_isSharedCheck_2389_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2370_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2389_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v_fvarId_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2385_; 
v_fvarId_2375_ = lean_ctor_get(v_decl_2342_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v_decl_2342_);
if (v_isSharedCheck_2385_ == 0)
{
lean_object* v_unused_2386_; lean_object* v_unused_2387_; lean_object* v_unused_2388_; 
v_unused_2386_ = lean_ctor_get(v_decl_2342_, 3);
lean_dec(v_unused_2386_);
v_unused_2387_ = lean_ctor_get(v_decl_2342_, 2);
lean_dec(v_unused_2387_);
v_unused_2388_ = lean_ctor_get(v_decl_2342_, 1);
lean_dec(v_unused_2388_);
v___x_2377_ = v_decl_2342_;
v_isShared_2378_ = v_isSharedCheck_2385_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_fvarId_2375_);
lean_dec(v_decl_2342_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2385_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
lean_inc(v_fvarId_2361_);
lean_inc(v_i_2367_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set_tag(v___x_2377_, 8);
lean_ctor_set(v___x_2377_, 3, v_a_2371_);
lean_ctor_set(v___x_2377_, 2, v_fvarId_2361_);
lean_ctor_set(v___x_2377_, 1, v_i_2367_);
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(8, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_fvarId_2375_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_i_2367_);
lean_ctor_set(v_reuseFailAlloc_2384_, 2, v_fvarId_2361_);
lean_ctor_set(v_reuseFailAlloc_2384_, 3, v_a_2371_);
v___x_2380_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
lean_object* v___x_2382_; 
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 0, v___x_2380_);
v___x_2382_ = v___x_2373_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2380_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
}
else
{
lean_dec_ref(v_decl_2342_);
return v___x_2370_;
}
}
case 3:
{
lean_object* v_offset_2390_; lean_object* v_type_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v_offset_2390_ = lean_ctor_get(v___x_2363_, 1);
v_type_2391_ = lean_ctor_get(v___x_2363_, 2);
v___x_2392_ = lean_unsigned_to_nat(1u);
v___x_2393_ = lean_nat_add(v_i_2347_, v___x_2392_);
lean_dec(v_i_2347_);
lean_inc_ref(v_decl_2342_);
v___x_2394_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2342_, v_k_2343_, v_ctorInfo_2344_, v_fields_2345_, v_irArgs_2346_, v___x_2393_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2407_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2397_ = v___x_2394_;
v_isShared_2398_ = v_isSharedCheck_2407_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2407_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v_fvarId_2399_; lean_object* v_size_2400_; lean_object* v_usize_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2405_; 
v_fvarId_2399_ = lean_ctor_get(v_decl_2342_, 0);
lean_inc(v_fvarId_2399_);
lean_dec_ref(v_decl_2342_);
v_size_2400_ = lean_ctor_get(v_ctorInfo_2344_, 2);
v_usize_2401_ = lean_ctor_get(v_ctorInfo_2344_, 3);
v___x_2402_ = lean_nat_add(v_size_2400_, v_usize_2401_);
lean_inc_ref(v_type_2391_);
lean_inc(v_fvarId_2361_);
lean_inc(v_offset_2390_);
v___x_2403_ = lean_alloc_ctor(9, 6, 0);
lean_ctor_set(v___x_2403_, 0, v_fvarId_2399_);
lean_ctor_set(v___x_2403_, 1, v___x_2402_);
lean_ctor_set(v___x_2403_, 2, v_offset_2390_);
lean_ctor_set(v___x_2403_, 3, v_fvarId_2361_);
lean_ctor_set(v___x_2403_, 4, v_type_2391_);
lean_ctor_set(v___x_2403_, 5, v_a_2395_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2403_);
v___x_2405_ = v___x_2397_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
else
{
lean_dec_ref(v_decl_2342_);
return v___x_2394_;
}
}
default: 
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = lean_unsigned_to_nat(1u);
v___x_2409_ = lean_nat_add(v_i_2347_, v___x_2408_);
lean_dec(v_i_2347_);
v_i_2347_ = v___x_2409_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(lean_object* v_decl_2411_, lean_object* v_k_2412_, lean_object* v_ctorInfo_2413_, lean_object* v_fields_2414_, lean_object* v_irArgs_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = lean_unsigned_to_nat(0u);
v___x_2423_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2411_, v_k_2412_, v_ctorInfo_2413_, v_fields_2414_, v_irArgs_2415_, v___x_2422_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields___boxed(lean_object* v_decl_2424_, lean_object* v_k_2425_, lean_object* v_ctorInfo_2426_, lean_object* v_fields_2427_, lean_object* v_irArgs_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields(v_decl_2424_, v_k_2425_, v_ctorInfo_2426_, v_fields_2427_, v_irArgs_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
lean_dec(v_a_2429_);
lean_dec_ref(v_irArgs_2428_);
lean_dec_ref(v_fields_2427_);
lean_dec_ref(v_ctorInfo_2426_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap___boxed(lean_object* v_decl_2436_, lean_object* v_k_2437_, lean_object* v_name_2438_, lean_object* v_args_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkPap(v_decl_2436_, v_k_2437_, v_name_2438_, v_args_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap___boxed(lean_object* v_decl_2447_, lean_object* v_k_2448_, lean_object* v_name_2449_, lean_object* v_args_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkFap(v_decl_2447_, v_k_2448_, v_name_2449_, v_args_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased___boxed(lean_object* v_k_2458_, lean_object* v_fvarId_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueErased(v_k_2458_, v_fvarId_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_);
lean_dec(v_a_2464_);
lean_dec_ref(v_a_2463_);
lean_dec(v_a_2462_);
lean_dec_ref(v_a_2461_);
lean_dec(v_a_2460_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication___boxed(lean_object* v_decl_2467_, lean_object* v_k_2468_, lean_object* v_name_2469_, lean_object* v_numParams_2470_, lean_object* v_args_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkApplication(v_decl_2467_, v_k_2468_, v_name_2469_, v_numParams_2470_, v_args_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
lean_dec(v_a_2472_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8___boxed(lean_object* v_fvarId_2479_, lean_object* v_sz_2480_, lean_object* v_i_2481_, lean_object* v_bs_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
size_t v_sz_boxed_2489_; size_t v_i_boxed_2490_; lean_object* v_res_2491_; 
v_sz_boxed_2489_ = lean_unbox_usize(v_sz_2480_);
lean_dec(v_sz_2480_);
v_i_boxed_2490_ = lean_unbox_usize(v_i_2481_);
lean_dec(v_i_2481_);
v_res_2491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__8(v_fvarId_2479_, v_sz_boxed_2489_, v_i_boxed_2490_, v_bs_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet___boxed(lean_object* v_k_2492_, lean_object* v_decl_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_continueLet(v_k_2492_, v_decl_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_);
lean_dec(v_a_2498_);
lean_dec_ref(v_a_2497_);
lean_dec(v_a_2496_);
lean_dec_ref(v_a_2495_);
lean_dec(v_a_2494_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure___boxed(lean_object* v_discr_2501_, lean_object* v_alt_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure(v_discr_2501_, v_alt_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_);
lean_dec(v_a_2507_);
lean_dec_ref(v_a_2506_);
lean_dec(v_a_2505_);
lean_dec_ref(v_a_2504_);
lean_dec(v_a_2503_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication___boxed(lean_object* v_decl_2510_, lean_object* v_k_2511_, lean_object* v_name_2512_, lean_object* v_numParams_2513_, lean_object* v_args_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_mkOverApplication(v_decl_2510_, v_k_2511_, v_name_2512_, v_numParams_2513_, v_args_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
lean_dec(v_a_2515_);
lean_dec_ref(v_args_2514_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop___boxed(lean_object* v_decl_2522_, lean_object* v_k_2523_, lean_object* v_ctorInfo_2524_, lean_object* v_fields_2525_, lean_object* v_irArgs_2526_, lean_object* v_i_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_lowerNonObjectFields_loop(v_decl_2522_, v_k_2523_, v_ctorInfo_2524_, v_fields_2525_, v_irArgs_2526_, v_i_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
lean_dec(v_a_2530_);
lean_dec_ref(v_a_2529_);
lean_dec(v_a_2528_);
lean_dec_ref(v_irArgs_2526_);
lean_dec_ref(v_fields_2525_);
lean_dec_ref(v_ctorInfo_2524_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop___boxed(lean_object* v_discr_2535_, lean_object* v_k_2536_, lean_object* v_ctorInfo_2537_, lean_object* v_params_2538_, lean_object* v_fields_2539_, lean_object* v_i_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Alt_toImpure_loop(v_discr_2535_, v_k_2536_, v_ctorInfo_2537_, v_params_2538_, v_fields_2539_, v_i_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
lean_dec(v_a_2543_);
lean_dec_ref(v_a_2542_);
lean_dec(v_a_2541_);
lean_dec_ref(v_fields_2539_);
lean_dec_ref(v_params_2538_);
lean_dec_ref(v_ctorInfo_2537_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure___boxed(lean_object* v_c_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_c_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet___boxed(lean_object* v_decl_2556_, lean_object* v_k_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet(v_decl_2556_, v_k_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
lean_dec(v_a_2562_);
lean_dec_ref(v_a_2561_);
lean_dec(v_a_2560_);
lean_dec_ref(v_a_2559_);
lean_dec(v_a_2558_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(lean_object* v_00_u03b1_2565_, lean_object* v_msg_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v_msg_2566_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___boxed(lean_object* v_00_u03b1_2574_, lean_object* v_msg_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12(v_00_u03b1_2574_, v_msg_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec(v___y_2576_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(size_t v_sz_2583_, size_t v_i_2584_, lean_object* v_bs_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2583_, v_i_2584_, v_bs_2585_, v___y_2586_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___boxed(lean_object* v_sz_2593_, lean_object* v_i_2594_, lean_object* v_bs_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
size_t v_sz_boxed_2602_; size_t v_i_boxed_2603_; lean_object* v_res_2604_; 
v_sz_boxed_2602_ = lean_unbox_usize(v_sz_2593_);
lean_dec(v_sz_2593_);
v_i_boxed_2603_ = lean_unbox_usize(v_i_2594_);
lean_dec(v_i_2594_);
v_res_2604_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2(v_sz_boxed_2602_, v_i_boxed_2603_, v_bs_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(lean_object* v_as_2605_, size_t v_i_2606_, size_t v_stop_2607_, lean_object* v_b_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___redArg(v_as_2605_, v_i_2606_, v_stop_2607_, v_b_2608_, v___y_2609_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6___boxed(lean_object* v_as_2616_, lean_object* v_i_2617_, lean_object* v_stop_2618_, lean_object* v_b_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_){
_start:
{
size_t v_i_boxed_2626_; size_t v_stop_boxed_2627_; lean_object* v_res_2628_; 
v_i_boxed_2626_ = lean_unbox_usize(v_i_2617_);
lean_dec(v_i_2617_);
v_stop_boxed_2627_ = lean_unbox_usize(v_stop_2618_);
lean_dec(v_stop_2618_);
v_res_2628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__6(v_as_2616_, v_i_boxed_2626_, v_stop_boxed_2627_, v_b_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v_as_2616_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(lean_object* v_upperBound_2629_, lean_object* v_params_2630_, lean_object* v___x_2631_, lean_object* v_discr_2632_, lean_object* v_inst_2633_, lean_object* v_R_2634_, lean_object* v_a_2635_, lean_object* v_b_2636_, lean_object* v_c_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___redArg(v_upperBound_2629_, v_params_2630_, v___x_2631_, v_discr_2632_, v_a_2635_, v_b_2636_, v___y_2638_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7___boxed(lean_object* v_upperBound_2645_, lean_object* v_params_2646_, lean_object* v___x_2647_, lean_object* v_discr_2648_, lean_object* v_inst_2649_, lean_object* v_R_2650_, lean_object* v_a_2651_, lean_object* v_b_2652_, lean_object* v_c_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__7(v_upperBound_2645_, v_params_2646_, v___x_2647_, v_discr_2648_, v_inst_2649_, v_R_2650_, v_a_2651_, v_b_2652_, v_c_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec(v___x_2647_);
lean_dec_ref(v_params_2646_);
lean_dec(v_upperBound_2645_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11(size_t v_sz_2661_, size_t v_i_2662_, lean_object* v_bs_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___redArg(v_sz_2661_, v_i_2662_, v_bs_2663_, v___y_2664_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11___boxed(lean_object* v_sz_2671_, lean_object* v_i_2672_, lean_object* v_bs_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
size_t v_sz_boxed_2680_; size_t v_i_boxed_2681_; lean_object* v_res_2682_; 
v_sz_boxed_2680_ = lean_unbox_usize(v_sz_2671_);
lean_dec(v_sz_2671_);
v_i_boxed_2681_ = lean_unbox_usize(v_i_2672_);
lean_dec(v_i_2672_);
v_res_2682_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__11(v_sz_boxed_2680_, v_i_boxed_2681_, v_bs_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(lean_object* v_upperBound_2683_, lean_object* v_fieldInfo_2684_, lean_object* v___x_2685_, lean_object* v_inst_2686_, lean_object* v_R_2687_, lean_object* v_a_2688_, lean_object* v_b_2689_, lean_object* v_c_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___redArg(v_upperBound_2683_, v_fieldInfo_2684_, v___x_2685_, v_a_2688_, v_b_2689_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13___boxed(lean_object* v_upperBound_2698_, lean_object* v_fieldInfo_2699_, lean_object* v___x_2700_, lean_object* v_inst_2701_, lean_object* v_R_2702_, lean_object* v_a_2703_, lean_object* v_b_2704_, lean_object* v_c_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__13(v_upperBound_2698_, v_fieldInfo_2699_, v___x_2700_, v_inst_2701_, v_R_2702_, v_a_2703_, v_b_2704_, v_c_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___x_2700_);
lean_dec_ref(v_fieldInfo_2699_);
lean_dec(v_upperBound_2698_);
return v_res_2712_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1(void){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__0));
v___x_2715_ = l_Lean_stringToMessageData(v___x_2714_);
return v___x_2715_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3(void){
_start:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__2));
v___x_2718_ = l_Lean_stringToMessageData(v___x_2717_);
return v___x_2718_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5(void){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2720_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__4));
v___x_2721_ = l_Lean_stringToMessageData(v___x_2720_);
return v___x_2721_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7(void){
_start:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2723_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__6));
v___x_2724_ = l_Lean_stringToMessageData(v___x_2723_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(lean_object* v_decl_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_){
_start:
{
lean_object* v_toSignature_2732_; lean_object* v_value_2733_; uint8_t v_recursive_2734_; lean_object* v_inlineAttr_x3f_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2867_; 
v_toSignature_2732_ = lean_ctor_get(v_decl_2725_, 0);
v_value_2733_ = lean_ctor_get(v_decl_2725_, 1);
v_recursive_2734_ = lean_ctor_get_uint8(v_decl_2725_, sizeof(void*)*3);
v_inlineAttr_x3f_2735_ = lean_ctor_get(v_decl_2725_, 2);
v_isSharedCheck_2867_ = !lean_is_exclusive(v_decl_2725_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2737_ = v_decl_2725_;
v_isShared_2738_ = v_isSharedCheck_2867_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_inlineAttr_x3f_2735_);
lean_inc(v_value_2733_);
lean_inc(v_toSignature_2732_);
lean_dec(v_decl_2725_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2867_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v_name_2739_; lean_object* v_levelParams_2740_; lean_object* v_type_2741_; lean_object* v_params_2742_; uint8_t v_safe_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2866_; 
v_name_2739_ = lean_ctor_get(v_toSignature_2732_, 0);
v_levelParams_2740_ = lean_ctor_get(v_toSignature_2732_, 1);
v_type_2741_ = lean_ctor_get(v_toSignature_2732_, 2);
v_params_2742_ = lean_ctor_get(v_toSignature_2732_, 3);
v_safe_2743_ = lean_ctor_get_uint8(v_toSignature_2732_, sizeof(void*)*4);
v_isSharedCheck_2866_ = !lean_is_exclusive(v_toSignature_2732_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2745_ = v_toSignature_2732_;
v_isShared_2746_ = v_isSharedCheck_2866_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_params_2742_);
lean_inc(v_type_2741_);
lean_inc(v_levelParams_2740_);
lean_inc(v_name_2739_);
lean_dec(v_toSignature_2732_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2866_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
size_t v_sz_2747_; size_t v___x_2748_; lean_object* v___x_2749_; 
v_sz_2747_ = lean_array_size(v_params_2742_);
v___x_2748_ = ((size_t)0ULL);
lean_inc_ref(v_params_2742_);
v___x_2749_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure_spec__2___redArg(v_sz_2747_, v___x_2748_, v_params_2742_, v_a_2726_, v_a_2728_, v_a_2729_, v_a_2730_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2749_, 1);
v___x_2751_ = lean_array_get_size(v_params_2742_);
lean_dec_ref(v_params_2742_);
v___x_2752_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_2741_, v___x_2751_, v_a_2729_, v_a_2730_);
lean_dec_ref(v_type_2741_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2849_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2755_ = v___x_2752_;
v_isShared_2756_ = v_isSharedCheck_2849_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2752_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2849_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2757_; lean_object* v_env_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; 
v___x_2757_ = lean_st_ref_get(v_a_2730_);
v_env_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc_ref(v_env_2758_);
lean_dec(v___x_2757_);
v___x_2759_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr;
lean_inc(v_name_2739_);
v___x_2760_ = l_Lean_TagAttribute_hasTag(v___x_2759_, v_env_2758_, v_name_2739_);
if (lean_obj_tag(v_value_2733_) == 0)
{
lean_object* v_code_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2811_; 
lean_del_object(v___x_2755_);
v_code_2761_ = lean_ctor_get(v_value_2733_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v_value_2733_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2763_ = v_value_2733_;
v_isShared_2764_ = v_isSharedCheck_2811_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_code_2761_);
lean_dec(v_value_2733_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2811_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; 
if (v___x_2760_ == 0)
{
v___y_2766_ = v_a_2726_;
v___y_2767_ = v_a_2727_;
v___y_2768_ = v_a_2728_;
v___y_2769_ = v_a_2729_;
v___y_2770_ = v_a_2730_;
goto v___jp_2765_;
}
else
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
lean_del_object(v___x_2763_);
lean_dec_ref(v_code_2761_);
lean_dec(v_a_2753_);
lean_dec(v_a_2750_);
lean_del_object(v___x_2745_);
lean_dec(v_levelParams_2740_);
lean_del_object(v___x_2737_);
lean_dec(v_inlineAttr_x3f_2735_);
v___x_2797_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__1);
v___x_2798_ = l_Lean_MessageData_ofName(v_name_2739_);
v___x_2799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2797_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
v___x_2800_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__3);
v___x_2801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2799_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
v___x_2802_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_2801_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_);
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2802_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2802_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
v___jp_2765_:
{
lean_object* v___x_2771_; 
v___x_2771_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Code_toImpure(v_code_2761_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2788_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2788_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2788_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 3, v_a_2750_);
lean_ctor_set(v___x_2745_, 2, v_a_2753_);
v___x_2777_ = v___x_2745_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_name_2739_);
lean_ctor_set(v_reuseFailAlloc_2787_, 1, v_levelParams_2740_);
lean_ctor_set(v_reuseFailAlloc_2787_, 2, v_a_2753_);
lean_ctor_set(v_reuseFailAlloc_2787_, 3, v_a_2750_);
lean_ctor_set_uint8(v_reuseFailAlloc_2787_, sizeof(void*)*4, v_safe_2743_);
v___x_2777_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
lean_object* v___x_2779_; 
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 0, v_a_2772_);
v___x_2779_ = v___x_2763_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2772_);
v___x_2779_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
lean_object* v___x_2781_; 
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 1, v___x_2779_);
lean_ctor_set(v___x_2737_, 0, v___x_2777_);
v___x_2781_ = v___x_2737_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v___x_2777_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v___x_2779_);
lean_ctor_set(v_reuseFailAlloc_2785_, 2, v_inlineAttr_x3f_2735_);
lean_ctor_set_uint8(v_reuseFailAlloc_2785_, sizeof(void*)*3, v_recursive_2734_);
v___x_2781_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2783_; 
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v___x_2781_);
v___x_2783_ = v___x_2774_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2781_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
}
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_del_object(v___x_2763_);
lean_dec(v_a_2753_);
lean_dec(v_a_2750_);
lean_del_object(v___x_2745_);
lean_dec(v_levelParams_2740_);
lean_dec(v_name_2739_);
lean_del_object(v___x_2737_);
lean_dec(v_inlineAttr_x3f_2735_);
v_a_2789_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2771_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2771_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
}
}
else
{
lean_object* v_externAttrData_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2848_; 
v_externAttrData_2812_ = lean_ctor_get(v_value_2733_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v_value_2733_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2814_ = v_value_2733_;
v_isShared_2815_ = v_isSharedCheck_2848_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_externAttrData_2812_);
lean_dec(v_value_2733_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2848_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v_resultType_2817_; 
if (v___x_2760_ == 0)
{
v_resultType_2817_ = v_a_2753_;
goto v___jp_2816_;
}
else
{
uint8_t v___x_2830_; 
v___x_2830_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_a_2753_);
if (v___x_2830_ == 0)
{
lean_object* v___x_2831_; 
lean_dec(v_a_2753_);
v___x_2831_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_litValueImpureType___closed__5);
v_resultType_2817_ = v___x_2831_;
goto v___jp_2816_;
}
else
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_del_object(v___x_2814_);
lean_dec(v_externAttrData_2812_);
lean_del_object(v___x_2755_);
lean_dec(v_a_2750_);
lean_del_object(v___x_2745_);
lean_dec(v_levelParams_2740_);
lean_del_object(v___x_2737_);
lean_dec(v_inlineAttr_x3f_2735_);
v___x_2832_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__5);
v___x_2833_ = l_Lean_MessageData_ofName(v_name_2739_);
v___x_2834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2832_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
v___x_2835_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___closed__7);
v___x_2836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2834_);
lean_ctor_set(v___x_2836_, 1, v___x_2835_);
v___x_2837_ = l_Lean_MessageData_ofExpr(v_a_2753_);
v___x_2838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2836_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_lowerLet_spec__12___redArg(v___x_2838_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_);
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
v___jp_2816_:
{
lean_object* v___x_2819_; 
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 3, v_a_2750_);
lean_ctor_set(v___x_2745_, 2, v_resultType_2817_);
v___x_2819_ = v___x_2745_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_name_2739_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_levelParams_2740_);
lean_ctor_set(v_reuseFailAlloc_2829_, 2, v_resultType_2817_);
lean_ctor_set(v_reuseFailAlloc_2829_, 3, v_a_2750_);
lean_ctor_set_uint8(v_reuseFailAlloc_2829_, sizeof(void*)*4, v_safe_2743_);
v___x_2819_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
lean_object* v___x_2821_; 
if (v_isShared_2815_ == 0)
{
v___x_2821_ = v___x_2814_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_externAttrData_2812_);
v___x_2821_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
lean_object* v___x_2823_; 
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 1, v___x_2821_);
lean_ctor_set(v___x_2737_, 0, v___x_2819_);
v___x_2823_ = v___x_2737_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2819_);
lean_ctor_set(v_reuseFailAlloc_2827_, 1, v___x_2821_);
lean_ctor_set(v_reuseFailAlloc_2827_, 2, v_inlineAttr_x3f_2735_);
lean_ctor_set_uint8(v_reuseFailAlloc_2827_, sizeof(void*)*3, v_recursive_2734_);
v___x_2823_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2825_; 
if (v_isShared_2756_ == 0)
{
lean_ctor_set(v___x_2755_, 0, v___x_2823_);
v___x_2825_ = v___x_2755_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
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
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_dec(v_a_2750_);
lean_del_object(v___x_2745_);
lean_dec(v_levelParams_2740_);
lean_dec(v_name_2739_);
lean_del_object(v___x_2737_);
lean_dec(v_inlineAttr_x3f_2735_);
lean_dec_ref(v_value_2733_);
v_a_2850_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2752_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2752_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_del_object(v___x_2745_);
lean_dec_ref(v_params_2742_);
lean_dec_ref(v_type_2741_);
lean_dec(v_levelParams_2740_);
lean_dec(v_name_2739_);
lean_del_object(v___x_2737_);
lean_dec(v_inlineAttr_x3f_2735_);
lean_dec_ref(v_value_2733_);
v_a_2858_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2749_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2749_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl___boxed(lean_object* v_decl_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(v_decl_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
lean_dec(v_a_2873_);
lean_dec_ref(v_a_2872_);
lean_dec(v_a_2871_);
lean_dec_ref(v_a_2870_);
lean_dec(v_a_2869_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(lean_object* v_decl_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_lowerDecl(v_decl_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v___x_2885_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc_n(v_a_2884_, 2);
lean_dec_ref_known(v___x_2883_, 1);
v___x_2885_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_a_2884_, v_a_2881_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2892_ == 0)
{
lean_object* v_unused_2893_; 
v_unused_2893_ = lean_ctor_get(v___x_2885_, 0);
lean_dec(v_unused_2893_);
v___x_2887_ = v___x_2885_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_dec(v___x_2885_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v_a_2884_);
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2884_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_dec(v_a_2884_);
v_a_2894_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2885_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2885_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
else
{
return v___x_2883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go___boxed(lean_object* v_decl_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(v_decl_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec(v_a_2905_);
lean_dec_ref(v_a_2904_);
lean_dec(v_a_2903_);
return v_res_2909_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0(void){
_start:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2910_ = lean_box(0);
v___x_2911_ = lean_unsigned_to_nat(16u);
v___x_2912_ = lean_mk_array(v___x_2911_, v___x_2910_);
return v___x_2912_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1(void){
_start:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2913_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__0);
v___x_2914_ = lean_unsigned_to_nat(0u);
v___x_2915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2914_);
lean_ctor_set(v___x_2915_, 1, v___x_2913_);
return v___x_2915_;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2(void){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__1);
v___x_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2916_);
lean_ctor_set(v___x_2917_, 1, v___x_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(lean_object* v_decl_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_){
_start:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2924_ = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2, &l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___closed__2);
v___x_2925_ = lean_st_mk_ref(v___x_2924_);
v___x_2926_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure_go(v_decl_2918_, v___x_2925_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2935_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2929_ = v___x_2926_;
v_isShared_2930_ = v_isSharedCheck_2935_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2926_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2935_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2931_; lean_object* v___x_2933_; 
v___x_2931_ = lean_st_ref_get(v___x_2925_);
lean_dec(v___x_2925_);
lean_dec(v___x_2931_);
if (v_isShared_2930_ == 0)
{
v___x_2933_ = v___x_2929_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2927_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
else
{
lean_dec(v___x_2925_);
return v___x_2926_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure___boxed(lean_object* v_decl_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(v_decl_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
lean_dec(v_a_2940_);
lean_dec_ref(v_a_2939_);
lean_dec(v_a_2938_);
lean_dec_ref(v_a_2937_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(size_t v_sz_2943_, size_t v_i_2944_, lean_object* v_bs_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
uint8_t v___x_2951_; 
v___x_2951_ = lean_usize_dec_lt(v_i_2944_, v_sz_2943_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; 
v___x_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2952_, 0, v_bs_2945_);
return v___x_2952_;
}
else
{
lean_object* v_v_2953_; lean_object* v___x_2954_; 
v_v_2953_ = lean_array_uget_borrowed(v_bs_2945_, v_i_2944_);
lean_inc(v_v_2953_);
v___x_2954_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_Decl_toImpure(v_v_2953_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v___x_2956_; lean_object* v_bs_x27_2957_; size_t v___x_2958_; size_t v___x_2959_; lean_object* v___x_2960_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_a_2955_);
lean_dec_ref_known(v___x_2954_, 1);
v___x_2956_ = lean_unsigned_to_nat(0u);
v_bs_x27_2957_ = lean_array_uset(v_bs_2945_, v_i_2944_, v___x_2956_);
v___x_2958_ = ((size_t)1ULL);
v___x_2959_ = lean_usize_add(v_i_2944_, v___x_2958_);
v___x_2960_ = lean_array_uset(v_bs_x27_2957_, v_i_2944_, v_a_2955_);
v_i_2944_ = v___x_2959_;
v_bs_2945_ = v___x_2960_;
goto _start;
}
else
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
lean_dec_ref(v_bs_2945_);
v_a_2962_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2964_ = v___x_2954_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2954_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2967_; 
if (v_isShared_2965_ == 0)
{
v___x_2967_ = v___x_2964_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2962_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0___boxed(lean_object* v_sz_2970_, lean_object* v_i_2971_, lean_object* v_bs_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
size_t v_sz_boxed_2978_; size_t v_i_boxed_2979_; lean_object* v_res_2980_; 
v_sz_boxed_2978_ = lean_unbox_usize(v_sz_2970_);
lean_dec(v_sz_2970_);
v_i_boxed_2979_ = lean_unbox_usize(v_i_2971_);
lean_dec(v_i_2971_);
v_res_2980_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(v_sz_boxed_2978_, v_i_boxed_2979_, v_bs_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0(lean_object* v_x_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
size_t v_sz_2987_; size_t v___x_2988_; lean_object* v___x_2989_; 
v_sz_2987_ = lean_array_size(v_x_2981_);
v___x_2988_ = ((size_t)0ULL);
v___x_2989_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toImpure_spec__0(v_sz_2987_, v___x_2988_, v_x_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toImpure___lam__0___boxed(lean_object* v_x_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_Lean_Compiler_LCNF_toImpure___lam__0(v_x_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3047_; uint8_t v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3047_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_));
v___x_3048_ = 1;
v___x_3049_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_));
v___x_3050_ = l_Lean_registerTraceClass(v___x_3047_, v___x_3048_, v___x_3049_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2____boxed(lean_object* v_a_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_6355896____hygCtx___hyg_2_();
return v_res_3052_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_ToImpureType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ToImpure(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpure_1721792695____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr);
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr___regBuiltin___private_Lean_Compiler_LCNF_ToImpure_0__Lean_Compiler_LCNF_taggedReturnAttr_declRange__3();
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
