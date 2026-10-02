// Lean compiler output
// Module: Lean.Meta.Constructions.CtorIdx
// Imports: public import Lean.Meta.Basic import Lean.AddDecl import Lean.Meta.CompletionName import Lean.Linter.Deprecated import Lean.Compiler.ImplementedByAttr import Lean.Compiler.LCNF.Util
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Lean_getMaxHeight(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isRuntimeBuiltinType(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_setImplementedBy(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "genCtorIdx"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(121, 142, 77, 16, 50, 110, 46, 202)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "generate the `CtorIdx` functions for inductive datatypes"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Constructions"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(224, 107, 212, 234, 74, 49, 105, 87)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CtorIdx"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(149, 119, 104, 54, 230, 159, 208, 234)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 246, 214, 203, 234, 6, 143, 204)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(57, 215, 55, 153, 7, 83, 44, 161)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(35, 209, 53, 49, 90, 19, 84, 123)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_genCtorIdx;
static const lean_string_object l_Lean_mkCtorIdxName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ctorIdx"};
static const lean_object* l_Lean_mkCtorIdxName___closed__0 = (const lean_object*)&l_Lean_mkCtorIdxName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdxName(lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImplName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_impl"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImplName___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImplName___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImplName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtorIdxCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "getObjTagNat"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(208, 128, 56, 123, 191, 118, 73, 69)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_mkCtorIdx_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_mkCtorIdx_spec__11___closed__0 = (const lean_object*)&l_panic___at___00Lean_mkCtorIdx_spec__11___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCtorIdx_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCtorIdx_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkCtorIdx___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCtorIdx___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCtorIdx___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_mkCtorIdx___lam__1___closed__0 = (const lean_object*)&l_Lean_mkCtorIdx___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_mkCtorIdx___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCtorIdx___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_mkCtorIdx___lam__1___closed__1 = (const lean_object*)&l_Lean_mkCtorIdx___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCtorIdx___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_mkCtorIdx___lam__2___closed__0 = (const lean_object*)&l_Lean_mkCtorIdx___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_mkCtorIdx___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCtorIdx___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_mkCtorIdx___lam__2___closed__1 = (const lean_object*)&l_Lean_mkCtorIdx___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCtorIdx___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Constructions.CtorIdx"};
static const lean_object* l_Lean_mkCtorIdx___lam__3___closed__0 = (const lean_object*)&l_Lean_mkCtorIdx___lam__3___closed__0_value;
static const lean_string_object l_Lean_mkCtorIdx___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.mkCtorIdx"};
static const lean_object* l_Lean_mkCtorIdx___lam__3___closed__1 = (const lean_object*)&l_Lean_mkCtorIdx___lam__3___closed__1_value;
static lean_once_cell_t l_Lean_mkCtorIdx___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCtorIdx___lam__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCtorIdx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "failed to construct `T.ctorIdx` for `"};
static const lean_object* l_Lean_mkCtorIdx___closed__0 = (const lean_object*)&l_Lean_mkCtorIdx___closed__0_value;
static lean_once_cell_t l_Lean_mkCtorIdx___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCtorIdx___closed__1;
static const lean_string_object l_Lean_mkCtorIdx___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`:"};
static const lean_object* l_Lean_mkCtorIdx___closed__2 = (const lean_object*)&l_Lean_mkCtorIdx___closed__2_value;
static lean_once_cell_t l_Lean_mkCtorIdx___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCtorIdx___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_74_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_75_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_76_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v___x_73_, v___x_74_, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4____boxed(lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdxName(lean_object* v_indName_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = ((lean_object*)(l_Lean_mkCtorIdxName___closed__0));
v___x_82_ = l_Lean_Name_str___override(v_indName_80_, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImplName(lean_object* v_indName_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = l_Lean_mkCtorIdxName(v_indName_84_);
v___x_86_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImplName___closed__0));
v___x_87_ = l_Lean_Name_str___override(v___x_85_, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdxCore_x3f(lean_object* v_env_88_, lean_object* v_declName_89_){
_start:
{
if (lean_obj_tag(v_declName_89_) == 1)
{
lean_object* v_pre_90_; lean_object* v_str_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v_pre_90_ = lean_ctor_get(v_declName_89_, 0);
lean_inc(v_pre_90_);
v_str_91_ = lean_ctor_get(v_declName_89_, 1);
lean_inc_ref(v_str_91_);
lean_dec_ref_known(v_declName_89_, 2);
v___x_92_ = ((lean_object*)(l_Lean_mkCtorIdxName___closed__0));
v___x_93_ = lean_string_dec_eq(v_str_91_, v___x_92_);
lean_dec_ref(v_str_91_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
lean_dec(v_pre_90_);
lean_dec_ref(v_env_88_);
v___x_94_ = lean_box(0);
return v___x_94_;
}
else
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_isInductiveCore_x3f(v_env_88_, v_pre_90_);
return v___x_95_;
}
}
else
{
lean_object* v___x_96_; 
lean_dec(v_declName_89_);
lean_dec_ref(v_env_88_);
v___x_96_ = lean_box(0);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___redArg(lean_object* v_declName_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_100_; lean_object* v_env_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_100_ = lean_st_ref_get(v_a_98_);
v_env_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc_ref(v_env_101_);
lean_dec(v___x_100_);
v___x_102_ = l_Lean_isCtorIdxCore_x3f(v_env_101_, v_declName_97_);
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___redArg___boxed(lean_object* v_declName_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_isCtorIdx_x3f___redArg(v_declName_104_, v_a_105_);
lean_dec(v_a_105_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f(lean_object* v_declName_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_isCtorIdx_x3f___redArg(v_declName_108_, v_a_112_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___boxed(lean_object* v_declName_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_isCtorIdx_x3f(v_declName_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
lean_dec(v_a_117_);
lean_dec_ref(v_a_116_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0(lean_object* v_k_122_, lean_object* v_b_123_, lean_object* v_c_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___x_130_; 
lean_inc(v___y_128_);
lean_inc_ref(v___y_127_);
lean_inc(v___y_126_);
lean_inc_ref(v___y_125_);
v___x_130_ = lean_apply_7(v_k_122_, v_b_123_, v_c_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, lean_box(0));
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0___boxed(lean_object* v_k_131_, lean_object* v_b_132_, lean_object* v_c_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0(v_k_131_, v_b_132_, v_c_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg(lean_object* v_type_140_, lean_object* v_k_141_, uint8_t v_cleanupAnnotations_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___f_148_; uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___f_148_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_148_, 0, v_k_141_);
v___x_149_ = 0;
v___x_150_ = lean_box(0);
v___x_151_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_149_, v___x_150_, v_type_140_, v___f_148_, v_cleanupAnnotations_142_, v___x_149_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_151_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_151_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
else
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
v_a_160_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_151_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_151_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___boxed(lean_object* v_type_168_, lean_object* v_k_169_, lean_object* v_cleanupAnnotations_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_176_; lean_object* v_res_177_; 
v_cleanupAnnotations_boxed_176_ = lean_unbox(v_cleanupAnnotations_170_);
v_res_177_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg(v_type_168_, v_k_169_, v_cleanupAnnotations_boxed_176_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0(lean_object* v_00_u03b1_178_, lean_object* v_type_179_, lean_object* v_k_180_, uint8_t v_cleanupAnnotations_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg(v_type_179_, v_k_180_, v_cleanupAnnotations_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___boxed(lean_object* v_00_u03b1_188_, lean_object* v_type_189_, lean_object* v_k_190_, lean_object* v_cleanupAnnotations_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_197_; lean_object* v_res_198_; 
v_cleanupAnnotations_boxed_197_ = lean_unbox(v_cleanupAnnotations_191_);
v_res_198_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0(v_00_u03b1_188_, v_type_189_, v_k_190_, v_cleanupAnnotations_boxed_197_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0(lean_object* v___x_202_, lean_object* v_args_203_, lean_object* v_x_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v_discr_213_; lean_object* v___x_214_; 
v___x_210_ = lean_array_get_size(v_args_203_);
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_sub(v___x_210_, v___x_211_);
v_discr_213_ = lean_array_get_borrowed(v___x_202_, v_args_203_, v___x_212_);
lean_dec(v___x_212_);
lean_inc(v___y_208_);
lean_inc_ref(v___y_207_);
lean_inc(v___y_206_);
lean_inc_ref(v___y_205_);
lean_inc(v_discr_213_);
v___x_214_ = lean_infer_type(v_discr_213_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; lean_object* v___x_216_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc_n(v_a_215_, 2);
lean_dec_ref_known(v___x_214_, 1);
v___x_216_ = l_Lean_Meta_getLevel(v_a_215_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; uint8_t v___x_224_; uint8_t v___x_225_; lean_object* v___x_226_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_a_217_);
lean_dec_ref_known(v___x_216_, 1);
v___x_218_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___closed__1));
v___x_219_ = lean_box(0);
v___x_220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_220_, 0, v_a_217_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
v___x_221_ = l_Lean_mkConst(v___x_218_, v___x_220_);
lean_inc(v_discr_213_);
v___x_222_ = l_Lean_mkAppB(v___x_221_, v_a_215_, v_discr_213_);
v___x_223_ = 0;
v___x_224_ = 1;
v___x_225_ = 1;
v___x_226_ = l_Lean_Meta_mkLambdaFVars(v_args_203_, v___x_222_, v___x_223_, v___x_224_, v___x_223_, v___x_224_, v___x_225_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
return v___x_226_;
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
lean_dec(v_a_215_);
v_a_227_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_216_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_216_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
else
{
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___boxed(lean_object* v___x_235_, lean_object* v_args_236_, lean_object* v_x_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0(v___x_235_, v_args_236_, v_x_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec_ref(v_x_237_);
lean_dec_ref(v_args_236_);
lean_dec_ref(v___x_235_);
return v_res_243_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__0(void){
_start:
{
lean_object* v___x_244_; lean_object* v___f_245_; 
v___x_244_ = l_Lean_instInhabitedExpr;
v___f_245_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___boxed), 8, 1);
lean_closure_set(v___f_245_, 0, v___x_244_);
return v___f_245_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1(void){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_246_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
return v___x_250_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2);
v___x_252_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
lean_ctor_set(v___x_252_, 2, v___x_251_);
lean_ctor_set(v___x_252_, 3, v___x_251_);
lean_ctor_set(v___x_252_, 4, v___x_251_);
lean_ctor_set(v___x_252_, 5, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl(lean_object* v_indName_253_, lean_object* v_levelParams_254_, lean_object* v_declType_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v___f_261_; lean_object* v_implName_262_; uint8_t v___x_263_; lean_object* v___x_264_; 
v___f_261_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__0, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__0_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__0);
lean_inc(v_indName_253_);
v_implName_262_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImplName(v_indName_253_);
v___x_263_ = 0;
lean_inc_ref(v_declType_255_);
v___x_264_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg(v_declType_255_, v___f_261_, v___x_263_, v_a_256_, v_a_257_, v_a_258_, v_a_259_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___y_274_; lean_object* v___y_275_; lean_object* v___y_276_; lean_object* v___y_277_; lean_object* v___x_306_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_a_265_);
lean_dec_ref_known(v___x_264_, 1);
lean_inc_n(v_implName_262_, 2);
v___x_266_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_266_, 0, v_implName_262_);
lean_ctor_set(v___x_266_, 1, v_levelParams_254_);
lean_ctor_set(v___x_266_, 2, v_declType_255_);
v___x_267_ = lean_box(0);
v___x_268_ = 0;
v___x_269_ = lean_box(0);
v___x_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_270_, 0, v_implName_262_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_271_, 0, v___x_266_);
lean_ctor_set(v___x_271_, 1, v_a_265_);
lean_ctor_set(v___x_271_, 2, v___x_267_);
lean_ctor_set(v___x_271_, 3, v___x_270_);
lean_ctor_set_uint8(v___x_271_, sizeof(void*)*4, v___x_268_);
v___x_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_inc_ref(v___x_272_);
v___x_306_ = l_Lean_addDecl(v___x_272_, v___x_263_, v_a_258_, v_a_259_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v___x_307_; lean_object* v_env_308_; lean_object* v_nextMacroScope_309_; lean_object* v_ngen_310_; lean_object* v_auxDeclNGen_311_; lean_object* v_traceState_312_; lean_object* v_recordedDeps_313_; lean_object* v_messages_314_; lean_object* v_infoState_315_; lean_object* v_snapshotTasks_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_412_; 
lean_dec_ref_known(v___x_306_, 1);
v___x_307_ = lean_st_ref_take(v_a_259_);
v_env_308_ = lean_ctor_get(v___x_307_, 0);
v_nextMacroScope_309_ = lean_ctor_get(v___x_307_, 1);
v_ngen_310_ = lean_ctor_get(v___x_307_, 2);
v_auxDeclNGen_311_ = lean_ctor_get(v___x_307_, 3);
v_traceState_312_ = lean_ctor_get(v___x_307_, 4);
v_recordedDeps_313_ = lean_ctor_get(v___x_307_, 6);
v_messages_314_ = lean_ctor_get(v___x_307_, 7);
v_infoState_315_ = lean_ctor_get(v___x_307_, 8);
v_snapshotTasks_316_ = lean_ctor_get(v___x_307_, 9);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; 
v_unused_413_ = lean_ctor_get(v___x_307_, 5);
lean_dec(v_unused_413_);
v___x_318_ = v___x_307_;
v_isShared_319_ = v_isSharedCheck_412_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_snapshotTasks_316_);
lean_inc(v_infoState_315_);
lean_inc(v_messages_314_);
lean_inc(v_recordedDeps_313_);
lean_inc(v_traceState_312_);
lean_inc(v_auxDeclNGen_311_);
lean_inc(v_ngen_310_);
lean_inc(v_nextMacroScope_309_);
lean_inc(v_env_308_);
lean_dec(v___x_307_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_412_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
lean_inc(v_implName_262_);
v___x_320_ = l_Lean_Meta_addToCompletionBlackList(v_env_308_, v_implName_262_);
v___x_321_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 5, v___x_321_);
lean_ctor_set(v___x_318_, 0, v___x_320_);
v___x_323_ = v___x_318_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_nextMacroScope_309_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_ngen_310_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_auxDeclNGen_311_);
lean_ctor_set(v_reuseFailAlloc_411_, 4, v_traceState_312_);
lean_ctor_set(v_reuseFailAlloc_411_, 5, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_411_, 6, v_recordedDeps_313_);
lean_ctor_set(v_reuseFailAlloc_411_, 7, v_messages_314_);
lean_ctor_set(v_reuseFailAlloc_411_, 8, v_infoState_315_);
lean_ctor_set(v_reuseFailAlloc_411_, 9, v_snapshotTasks_316_);
v___x_323_ = v_reuseFailAlloc_411_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v_mctx_326_; lean_object* v_zetaDeltaFVarIds_327_; lean_object* v_postponed_328_; lean_object* v_diag_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_409_; 
v___x_324_ = lean_st_ref_put(v_a_259_, v___x_323_);
v___x_325_ = lean_st_ref_take(v_a_257_);
v_mctx_326_ = lean_ctor_get(v___x_325_, 0);
v_zetaDeltaFVarIds_327_ = lean_ctor_get(v___x_325_, 2);
v_postponed_328_ = lean_ctor_get(v___x_325_, 3);
v_diag_329_ = lean_ctor_get(v___x_325_, 4);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; 
v_unused_410_ = lean_ctor_get(v___x_325_, 1);
lean_dec(v_unused_410_);
v___x_331_ = v___x_325_;
v_isShared_332_ = v_isSharedCheck_409_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_diag_329_);
lean_inc(v_postponed_328_);
lean_inc(v_zetaDeltaFVarIds_327_);
lean_inc(v_mctx_326_);
lean_dec(v___x_325_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_409_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_333_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 1, v___x_333_);
v___x_335_ = v___x_331_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_mctx_326_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_zetaDeltaFVarIds_327_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_postponed_328_);
lean_ctor_set(v_reuseFailAlloc_408_, 4, v_diag_329_);
v___x_335_ = v_reuseFailAlloc_408_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v_env_338_; lean_object* v_nextMacroScope_339_; lean_object* v_ngen_340_; lean_object* v_auxDeclNGen_341_; lean_object* v_traceState_342_; lean_object* v_recordedDeps_343_; lean_object* v_messages_344_; lean_object* v_infoState_345_; lean_object* v_snapshotTasks_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_406_; 
v___x_336_ = lean_st_ref_put(v_a_257_, v___x_335_);
v___x_337_ = lean_st_ref_take(v_a_259_);
v_env_338_ = lean_ctor_get(v___x_337_, 0);
v_nextMacroScope_339_ = lean_ctor_get(v___x_337_, 1);
v_ngen_340_ = lean_ctor_get(v___x_337_, 2);
v_auxDeclNGen_341_ = lean_ctor_get(v___x_337_, 3);
v_traceState_342_ = lean_ctor_get(v___x_337_, 4);
v_recordedDeps_343_ = lean_ctor_get(v___x_337_, 6);
v_messages_344_ = lean_ctor_get(v___x_337_, 7);
v_infoState_345_ = lean_ctor_get(v___x_337_, 8);
v_snapshotTasks_346_ = lean_ctor_get(v___x_337_, 9);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; 
v_unused_407_ = lean_ctor_get(v___x_337_, 5);
lean_dec(v_unused_407_);
v___x_348_ = v___x_337_;
v_isShared_349_ = v_isSharedCheck_406_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_snapshotTasks_346_);
lean_inc(v_infoState_345_);
lean_inc(v_messages_344_);
lean_inc(v_recordedDeps_343_);
lean_inc(v_traceState_342_);
lean_inc(v_auxDeclNGen_341_);
lean_inc(v_ngen_340_);
lean_inc(v_nextMacroScope_339_);
lean_inc(v_env_338_);
lean_dec(v___x_337_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_406_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_352_; 
lean_inc(v_implName_262_);
v___x_350_ = l_Lean_addProtected(v_env_338_, v_implName_262_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 5, v___x_321_);
lean_ctor_set(v___x_348_, 0, v___x_350_);
v___x_352_ = v___x_348_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_nextMacroScope_339_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v_ngen_340_);
lean_ctor_set(v_reuseFailAlloc_405_, 3, v_auxDeclNGen_341_);
lean_ctor_set(v_reuseFailAlloc_405_, 4, v_traceState_342_);
lean_ctor_set(v_reuseFailAlloc_405_, 5, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_405_, 6, v_recordedDeps_343_);
lean_ctor_set(v_reuseFailAlloc_405_, 7, v_messages_344_);
lean_ctor_set(v_reuseFailAlloc_405_, 8, v_infoState_345_);
lean_ctor_set(v_reuseFailAlloc_405_, 9, v_snapshotTasks_346_);
v___x_352_ = v_reuseFailAlloc_405_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v_mctx_355_; lean_object* v_zetaDeltaFVarIds_356_; lean_object* v_postponed_357_; lean_object* v_diag_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_403_; 
v___x_353_ = lean_st_ref_put(v_a_259_, v___x_352_);
v___x_354_ = lean_st_ref_take(v_a_257_);
v_mctx_355_ = lean_ctor_get(v___x_354_, 0);
v_zetaDeltaFVarIds_356_ = lean_ctor_get(v___x_354_, 2);
v_postponed_357_ = lean_ctor_get(v___x_354_, 3);
v_diag_358_ = lean_ctor_get(v___x_354_, 4);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; 
v_unused_404_ = lean_ctor_get(v___x_354_, 1);
lean_dec(v_unused_404_);
v___x_360_ = v___x_354_;
v_isShared_361_ = v_isSharedCheck_403_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_diag_358_);
lean_inc(v_postponed_357_);
lean_inc(v_zetaDeltaFVarIds_356_);
lean_inc(v_mctx_355_);
lean_dec(v___x_354_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_403_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v___x_333_);
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_mctx_355_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v_zetaDeltaFVarIds_356_);
lean_ctor_set(v_reuseFailAlloc_402_, 3, v_postponed_357_);
lean_ctor_set(v_reuseFailAlloc_402_, 4, v_diag_358_);
v___x_363_ = v_reuseFailAlloc_402_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v_env_366_; uint8_t v___x_367_; 
v___x_364_ = lean_st_ref_put(v_a_257_, v___x_363_);
v___x_365_ = lean_st_ref_get(v_a_259_);
v_env_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc_ref(v_env_366_);
lean_dec(v___x_365_);
v___x_367_ = l_Lean_isMarkedMeta(v_env_366_, v_indName_253_);
if (v___x_367_ == 0)
{
v___y_274_ = v_a_256_;
v___y_275_ = v_a_257_;
v___y_276_ = v_a_258_;
v___y_277_ = v_a_259_;
goto v___jp_273_;
}
else
{
lean_object* v___x_368_; lean_object* v_env_369_; lean_object* v_nextMacroScope_370_; lean_object* v_ngen_371_; lean_object* v_auxDeclNGen_372_; lean_object* v_traceState_373_; lean_object* v_recordedDeps_374_; lean_object* v_messages_375_; lean_object* v_infoState_376_; lean_object* v_snapshotTasks_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_400_; 
v___x_368_ = lean_st_ref_take(v_a_259_);
v_env_369_ = lean_ctor_get(v___x_368_, 0);
v_nextMacroScope_370_ = lean_ctor_get(v___x_368_, 1);
v_ngen_371_ = lean_ctor_get(v___x_368_, 2);
v_auxDeclNGen_372_ = lean_ctor_get(v___x_368_, 3);
v_traceState_373_ = lean_ctor_get(v___x_368_, 4);
v_recordedDeps_374_ = lean_ctor_get(v___x_368_, 6);
v_messages_375_ = lean_ctor_get(v___x_368_, 7);
v_infoState_376_ = lean_ctor_get(v___x_368_, 8);
v_snapshotTasks_377_ = lean_ctor_get(v___x_368_, 9);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_400_ == 0)
{
lean_object* v_unused_401_; 
v_unused_401_ = lean_ctor_get(v___x_368_, 5);
lean_dec(v_unused_401_);
v___x_379_ = v___x_368_;
v_isShared_380_ = v_isSharedCheck_400_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_snapshotTasks_377_);
lean_inc(v_infoState_376_);
lean_inc(v_messages_375_);
lean_inc(v_recordedDeps_374_);
lean_inc(v_traceState_373_);
lean_inc(v_auxDeclNGen_372_);
lean_inc(v_ngen_371_);
lean_inc(v_nextMacroScope_370_);
lean_inc(v_env_369_);
lean_dec(v___x_368_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_400_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_383_; 
lean_inc(v_implName_262_);
v___x_381_ = l_Lean_markMeta(v_env_369_, v_implName_262_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 5, v___x_321_);
lean_ctor_set(v___x_379_, 0, v___x_381_);
v___x_383_ = v___x_379_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_nextMacroScope_370_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v_ngen_371_);
lean_ctor_set(v_reuseFailAlloc_399_, 3, v_auxDeclNGen_372_);
lean_ctor_set(v_reuseFailAlloc_399_, 4, v_traceState_373_);
lean_ctor_set(v_reuseFailAlloc_399_, 5, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_399_, 6, v_recordedDeps_374_);
lean_ctor_set(v_reuseFailAlloc_399_, 7, v_messages_375_);
lean_ctor_set(v_reuseFailAlloc_399_, 8, v_infoState_376_);
lean_ctor_set(v_reuseFailAlloc_399_, 9, v_snapshotTasks_377_);
v___x_383_ = v_reuseFailAlloc_399_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v_mctx_386_; lean_object* v_zetaDeltaFVarIds_387_; lean_object* v_postponed_388_; lean_object* v_diag_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_397_; 
v___x_384_ = lean_st_ref_put(v_a_259_, v___x_383_);
v___x_385_ = lean_st_ref_take(v_a_257_);
v_mctx_386_ = lean_ctor_get(v___x_385_, 0);
v_zetaDeltaFVarIds_387_ = lean_ctor_get(v___x_385_, 2);
v_postponed_388_ = lean_ctor_get(v___x_385_, 3);
v_diag_389_ = lean_ctor_get(v___x_385_, 4);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v___x_385_, 1);
lean_dec(v_unused_398_);
v___x_391_ = v___x_385_;
v_isShared_392_ = v_isSharedCheck_397_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_diag_389_);
lean_inc(v_postponed_388_);
lean_inc(v_zetaDeltaFVarIds_387_);
lean_inc(v_mctx_386_);
lean_dec(v___x_385_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_397_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 1, v___x_333_);
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_mctx_386_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v_zetaDeltaFVarIds_387_);
lean_ctor_set(v_reuseFailAlloc_396_, 3, v_postponed_388_);
lean_ctor_set(v_reuseFailAlloc_396_, 4, v_diag_389_);
v___x_394_ = v_reuseFailAlloc_396_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_395_; 
v___x_395_ = lean_st_ref_put(v_a_257_, v___x_394_);
v___y_274_ = v_a_256_;
v___y_275_ = v_a_257_;
v___y_276_ = v_a_258_;
v___y_277_ = v_a_259_;
goto v___jp_273_;
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
}
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec_ref_known(v___x_272_, 1);
lean_dec(v_implName_262_);
lean_dec(v_indName_253_);
v_a_414_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_306_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_306_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
v___jp_273_:
{
uint8_t v___x_278_; lean_object* v___x_279_; 
v___x_278_ = 4;
lean_inc(v_implName_262_);
v___x_279_ = l_Lean_Meta_setInlineAttribute(v_implName_262_, v___x_278_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
if (lean_obj_tag(v___x_279_) == 0)
{
uint8_t v___x_280_; lean_object* v___x_281_; 
lean_dec_ref_known(v___x_279_, 1);
v___x_280_ = 1;
v___x_281_ = l_Lean_compileDecl(v___x_272_, v___x_280_, v___y_276_, v___y_277_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_288_ == 0)
{
lean_object* v_unused_289_; 
v_unused_289_ = lean_ctor_get(v___x_281_, 0);
lean_dec(v_unused_289_);
v___x_283_ = v___x_281_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_dec(v___x_281_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v_implName_262_);
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_implName_262_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_dec(v_implName_262_);
v_a_290_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_281_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_281_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec_ref_known(v___x_272_, 1);
lean_dec(v_implName_262_);
v_a_298_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_279_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_279_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec(v_implName_262_);
lean_dec_ref(v_declType_255_);
lean_dec(v_levelParams_254_);
lean_dec(v_indName_253_);
v_a_422_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_264_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_264_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___boxed(lean_object* v_indName_430_, lean_object* v_levelParams_431_, lean_object* v_declType_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl(v_indName_430_, v_levelParams_431_, v_declType_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
return v_res_438_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(lean_object* v_opts_439_, lean_object* v_opt_440_){
_start:
{
lean_object* v_name_441_; lean_object* v_defValue_442_; lean_object* v_map_443_; lean_object* v___x_444_; 
v_name_441_ = lean_ctor_get(v_opt_440_, 0);
v_defValue_442_ = lean_ctor_get(v_opt_440_, 1);
v_map_443_ = lean_ctor_get(v_opts_439_, 0);
v___x_444_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_443_, v_name_441_);
if (lean_obj_tag(v___x_444_) == 0)
{
uint8_t v___x_445_; 
v___x_445_ = lean_unbox(v_defValue_442_);
return v___x_445_;
}
else
{
lean_object* v_val_446_; 
v_val_446_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_val_446_);
lean_dec_ref_known(v___x_444_, 1);
if (lean_obj_tag(v_val_446_) == 1)
{
uint8_t v_v_447_; 
v_v_447_ = lean_ctor_get_uint8(v_val_446_, 0);
lean_dec_ref_known(v_val_446_, 0);
return v_v_447_;
}
else
{
uint8_t v___x_448_; 
lean_dec(v_val_446_);
v___x_448_ = lean_unbox(v_defValue_442_);
return v___x_448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0___boxed(lean_object* v_opts_449_, lean_object* v_opt_450_){
_start:
{
uint8_t v_res_451_; lean_object* v_r_452_; 
v_res_451_ = l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(v_opts_449_, v_opt_450_);
lean_dec_ref(v_opt_450_);
lean_dec_ref(v_opts_449_);
v_r_452_ = lean_box(v_res_451_);
return v_r_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(lean_object* v_constName_453_, uint8_t v_skipRealize_454_, lean_object* v___y_455_){
_start:
{
lean_object* v___x_457_; lean_object* v_env_458_; uint8_t v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_457_ = lean_st_ref_get(v___y_455_);
v_env_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc_ref(v_env_458_);
lean_dec(v___x_457_);
v___x_459_ = l_Lean_Environment_contains(v_env_458_, v_constName_453_, v_skipRealize_454_);
v___x_460_ = lean_box(v___x_459_);
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg___boxed(lean_object* v_constName_462_, lean_object* v_skipRealize_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
uint8_t v_skipRealize_boxed_466_; lean_object* v_res_467_; 
v_skipRealize_boxed_466_ = lean_unbox(v_skipRealize_463_);
v_res_467_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v_constName_462_, v_skipRealize_boxed_466_, v___y_464_);
lean_dec(v___y_464_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1(lean_object* v_constName_468_, uint8_t v_skipRealize_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v_constName_468_, v_skipRealize_469_, v___y_473_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___boxed(lean_object* v_constName_476_, lean_object* v_skipRealize_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
uint8_t v_skipRealize_boxed_483_; lean_object* v_res_484_; 
v_skipRealize_boxed_483_ = lean_unbox(v_skipRealize_477_);
v_res_484_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1(v_constName_476_, v_skipRealize_boxed_483_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(lean_object* v_type_485_, lean_object* v_maxFVars_x3f_486_, lean_object* v_k_487_, uint8_t v_cleanupAnnotations_488_, uint8_t v_whnfType_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___f_495_; lean_object* v___x_496_; 
v___f_495_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_495_, 0, v_k_487_);
v___x_496_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_485_, v_maxFVars_x3f_486_, v___f_495_, v_cleanupAnnotations_488_, v_whnfType_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
v_a_505_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_496_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_496_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___boxed(lean_object* v_type_513_, lean_object* v_maxFVars_x3f_514_, lean_object* v_k_515_, lean_object* v_cleanupAnnotations_516_, lean_object* v_whnfType_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_523_; uint8_t v_whnfType_boxed_524_; lean_object* v_res_525_; 
v_cleanupAnnotations_boxed_523_ = lean_unbox(v_cleanupAnnotations_516_);
v_whnfType_boxed_524_ = lean_unbox(v_whnfType_517_);
v_res_525_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_513_, v_maxFVars_x3f_514_, v_k_515_, v_cleanupAnnotations_boxed_523_, v_whnfType_boxed_524_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5(lean_object* v_00_u03b1_526_, lean_object* v_type_527_, lean_object* v_maxFVars_x3f_528_, lean_object* v_k_529_, uint8_t v_cleanupAnnotations_530_, uint8_t v_whnfType_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_527_, v_maxFVars_x3f_528_, v_k_529_, v_cleanupAnnotations_530_, v_whnfType_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___boxed(lean_object* v_00_u03b1_538_, lean_object* v_type_539_, lean_object* v_maxFVars_x3f_540_, lean_object* v_k_541_, lean_object* v_cleanupAnnotations_542_, lean_object* v_whnfType_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_549_; uint8_t v_whnfType_boxed_550_; lean_object* v_res_551_; 
v_cleanupAnnotations_boxed_549_ = lean_unbox(v_cleanupAnnotations_542_);
v_whnfType_boxed_550_ = lean_unbox(v_whnfType_543_);
v_res_551_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5(v_00_u03b1_538_, v_type_539_, v_maxFVars_x3f_540_, v_k_541_, v_cleanupAnnotations_boxed_549_, v_whnfType_boxed_550_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(lean_object* v_name_552_, lean_object* v_levelParams_553_, lean_object* v_type_554_, lean_object* v_value_555_, lean_object* v_hints_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; uint8_t v___y_561_; uint8_t v___y_568_; lean_object* v_env_571_; uint8_t v___x_572_; 
v___x_559_ = lean_st_ref_get(v___y_557_);
v_env_571_ = lean_ctor_get(v___x_559_, 0);
lean_inc_ref_n(v_env_571_, 2);
lean_dec(v___x_559_);
v___x_572_ = l_Lean_Environment_hasUnsafe(v_env_571_, v_type_554_);
if (v___x_572_ == 0)
{
uint8_t v___x_573_; 
v___x_573_ = l_Lean_Environment_hasUnsafe(v_env_571_, v_value_555_);
v___y_568_ = v___x_573_;
goto v___jp_567_;
}
else
{
lean_dec_ref(v_env_571_);
v___y_568_ = v___x_572_;
goto v___jp_567_;
}
v___jp_560_:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
lean_inc(v_name_552_);
v___x_562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_562_, 0, v_name_552_);
lean_ctor_set(v___x_562_, 1, v_levelParams_553_);
lean_ctor_set(v___x_562_, 2, v_type_554_);
v___x_563_ = lean_box(0);
v___x_564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_564_, 0, v_name_552_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_565_, 0, v___x_562_);
lean_ctor_set(v___x_565_, 1, v_value_555_);
lean_ctor_set(v___x_565_, 2, v_hints_556_);
lean_ctor_set(v___x_565_, 3, v___x_564_);
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*4, v___y_561_);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
v___jp_567_:
{
if (v___y_568_ == 0)
{
uint8_t v___x_569_; 
v___x_569_ = 1;
v___y_561_ = v___x_569_;
goto v___jp_560_;
}
else
{
uint8_t v___x_570_; 
v___x_570_ = 0;
v___y_561_ = v___x_570_;
goto v___jp_560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg___boxed(lean_object* v_name_574_, lean_object* v_levelParams_575_, lean_object* v_type_576_, lean_object* v_value_577_, lean_object* v_hints_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v_name_574_, v_levelParams_575_, v_type_576_, v_value_577_, v_hints_578_, v___y_579_);
lean_dec(v___y_579_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8(lean_object* v_name_582_, lean_object* v_levelParams_583_, lean_object* v_type_584_, lean_object* v_value_585_, lean_object* v_hints_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v_name_582_, v_levelParams_583_, v_type_584_, v_value_585_, v_hints_586_, v___y_590_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___boxed(lean_object* v_name_593_, lean_object* v_levelParams_594_, lean_object* v_type_595_, lean_object* v_value_596_, lean_object* v_hints_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8(v_name_593_, v_levelParams_594_, v_type_595_, v_value_596_, v_hints_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCtorIdx_spec__11(lean_object* v_msg_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v___f_611_; lean_object* v___x_12996__overap_612_; lean_object* v___x_613_; 
v___f_611_ = ((lean_object*)(l_panic___at___00Lean_mkCtorIdx_spec__11___closed__0));
v___x_12996__overap_612_ = lean_panic_fn_borrowed(v___f_611_, v_msg_605_);
lean_inc(v___y_609_);
lean_inc_ref(v___y_608_);
lean_inc(v___y_607_);
lean_inc_ref(v___y_606_);
v___x_613_ = lean_apply_5(v___x_12996__overap_612_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, lean_box(0));
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCtorIdx_spec__11___boxed(lean_object* v_msg_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_panic___at___00Lean_mkCtorIdx_spec__11(v_msg_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0(lean_object* v___y_621_, uint8_t v_isExporting_622_, lean_object* v___x_623_, lean_object* v___y_624_, lean_object* v___x_625_, lean_object* v_a_x3f_626_){
_start:
{
lean_object* v___x_628_; lean_object* v_env_629_; lean_object* v_nextMacroScope_630_; lean_object* v_ngen_631_; lean_object* v_auxDeclNGen_632_; lean_object* v_traceState_633_; lean_object* v_recordedDeps_634_; lean_object* v_messages_635_; lean_object* v_infoState_636_; lean_object* v_snapshotTasks_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_662_; 
v___x_628_ = lean_st_ref_take(v___y_621_);
v_env_629_ = lean_ctor_get(v___x_628_, 0);
v_nextMacroScope_630_ = lean_ctor_get(v___x_628_, 1);
v_ngen_631_ = lean_ctor_get(v___x_628_, 2);
v_auxDeclNGen_632_ = lean_ctor_get(v___x_628_, 3);
v_traceState_633_ = lean_ctor_get(v___x_628_, 4);
v_recordedDeps_634_ = lean_ctor_get(v___x_628_, 6);
v_messages_635_ = lean_ctor_get(v___x_628_, 7);
v_infoState_636_ = lean_ctor_get(v___x_628_, 8);
v_snapshotTasks_637_ = lean_ctor_get(v___x_628_, 9);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_662_ == 0)
{
lean_object* v_unused_663_; 
v_unused_663_ = lean_ctor_get(v___x_628_, 5);
lean_dec(v_unused_663_);
v___x_639_ = v___x_628_;
v_isShared_640_ = v_isSharedCheck_662_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_snapshotTasks_637_);
lean_inc(v_infoState_636_);
lean_inc(v_messages_635_);
lean_inc(v_recordedDeps_634_);
lean_inc(v_traceState_633_);
lean_inc(v_auxDeclNGen_632_);
lean_inc(v_ngen_631_);
lean_inc(v_nextMacroScope_630_);
lean_inc(v_env_629_);
lean_dec(v___x_628_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_662_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_641_ = l_Lean_Environment_setExporting(v_env_629_, v_isExporting_622_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 5, v___x_623_);
lean_ctor_set(v___x_639_, 0, v___x_641_);
v___x_643_ = v___x_639_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_nextMacroScope_630_);
lean_ctor_set(v_reuseFailAlloc_661_, 2, v_ngen_631_);
lean_ctor_set(v_reuseFailAlloc_661_, 3, v_auxDeclNGen_632_);
lean_ctor_set(v_reuseFailAlloc_661_, 4, v_traceState_633_);
lean_ctor_set(v_reuseFailAlloc_661_, 5, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_661_, 6, v_recordedDeps_634_);
lean_ctor_set(v_reuseFailAlloc_661_, 7, v_messages_635_);
lean_ctor_set(v_reuseFailAlloc_661_, 8, v_infoState_636_);
lean_ctor_set(v_reuseFailAlloc_661_, 9, v_snapshotTasks_637_);
v___x_643_ = v_reuseFailAlloc_661_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v_mctx_646_; lean_object* v_zetaDeltaFVarIds_647_; lean_object* v_postponed_648_; lean_object* v_diag_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_659_; 
v___x_644_ = lean_st_ref_put(v___y_621_, v___x_643_);
v___x_645_ = lean_st_ref_take(v___y_624_);
v_mctx_646_ = lean_ctor_get(v___x_645_, 0);
v_zetaDeltaFVarIds_647_ = lean_ctor_get(v___x_645_, 2);
v_postponed_648_ = lean_ctor_get(v___x_645_, 3);
v_diag_649_ = lean_ctor_get(v___x_645_, 4);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_659_ == 0)
{
lean_object* v_unused_660_; 
v_unused_660_ = lean_ctor_get(v___x_645_, 1);
lean_dec(v_unused_660_);
v___x_651_ = v___x_645_;
v_isShared_652_ = v_isSharedCheck_659_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_diag_649_);
lean_inc(v_postponed_648_);
lean_inc(v_zetaDeltaFVarIds_647_);
lean_inc(v_mctx_646_);
lean_dec(v___x_645_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_659_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_653_ = lean_box(0);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 1, v___x_625_);
v___x_655_ = v___x_651_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_mctx_646_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_658_, 2, v_zetaDeltaFVarIds_647_);
lean_ctor_set(v_reuseFailAlloc_658_, 3, v_postponed_648_);
lean_ctor_set(v_reuseFailAlloc_658_, 4, v_diag_649_);
v___x_655_ = v_reuseFailAlloc_658_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_st_ref_put(v___y_624_, v___x_655_);
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_653_);
return v___x_657_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0___boxed(lean_object* v___y_664_, lean_object* v_isExporting_665_, lean_object* v___x_666_, lean_object* v___y_667_, lean_object* v___x_668_, lean_object* v_a_x3f_669_, lean_object* v___y_670_){
_start:
{
uint8_t v_isExporting_boxed_671_; lean_object* v_res_672_; 
v_isExporting_boxed_671_ = lean_unbox(v_isExporting_665_);
v_res_672_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0(v___y_664_, v_isExporting_boxed_671_, v___x_666_, v___y_667_, v___x_668_, v_a_x3f_669_);
lean_dec(v_a_x3f_669_);
lean_dec(v___y_667_);
lean_dec(v___y_664_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(lean_object* v_x_673_, uint8_t v_isExporting_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v___x_680_; lean_object* v_env_681_; lean_object* v___x_682_; uint8_t v_isModule_683_; 
v___x_680_ = lean_st_ref_get(v___y_678_);
v_env_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc_ref(v_env_681_);
lean_dec(v___x_680_);
v___x_682_ = l_Lean_Environment_header(v_env_681_);
v_isModule_683_ = lean_ctor_get_uint8(v___x_682_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_682_);
if (v_isModule_683_ == 0)
{
lean_object* v___x_684_; 
lean_dec_ref(v_env_681_);
lean_inc(v___y_678_);
lean_inc_ref(v___y_677_);
lean_inc(v___y_676_);
lean_inc_ref(v___y_675_);
v___x_684_ = lean_apply_5(v_x_673_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, lean_box(0));
return v___x_684_;
}
else
{
uint8_t v_isExporting_685_; 
v_isExporting_685_ = lean_ctor_get_uint8(v_env_681_, sizeof(void*)*8);
lean_dec_ref(v_env_681_);
if (v_isExporting_674_ == 0)
{
if (v_isExporting_685_ == 0)
{
lean_object* v___x_752_; 
lean_inc(v___y_678_);
lean_inc_ref(v___y_677_);
lean_inc(v___y_676_);
lean_inc_ref(v___y_675_);
v___x_752_ = lean_apply_5(v_x_673_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, lean_box(0));
return v___x_752_;
}
else
{
goto v___jp_686_;
}
}
else
{
if (v_isExporting_685_ == 0)
{
goto v___jp_686_;
}
else
{
lean_object* v___x_753_; 
lean_inc(v___y_678_);
lean_inc_ref(v___y_677_);
lean_inc(v___y_676_);
lean_inc_ref(v___y_675_);
v___x_753_ = lean_apply_5(v_x_673_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, lean_box(0));
return v___x_753_;
}
}
v___jp_686_:
{
lean_object* v___x_687_; lean_object* v_env_688_; lean_object* v_nextMacroScope_689_; lean_object* v_ngen_690_; lean_object* v_auxDeclNGen_691_; lean_object* v_traceState_692_; lean_object* v_recordedDeps_693_; lean_object* v_messages_694_; lean_object* v_infoState_695_; lean_object* v_snapshotTasks_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_750_; 
v___x_687_ = lean_st_ref_take(v___y_678_);
v_env_688_ = lean_ctor_get(v___x_687_, 0);
v_nextMacroScope_689_ = lean_ctor_get(v___x_687_, 1);
v_ngen_690_ = lean_ctor_get(v___x_687_, 2);
v_auxDeclNGen_691_ = lean_ctor_get(v___x_687_, 3);
v_traceState_692_ = lean_ctor_get(v___x_687_, 4);
v_recordedDeps_693_ = lean_ctor_get(v___x_687_, 6);
v_messages_694_ = lean_ctor_get(v___x_687_, 7);
v_infoState_695_ = lean_ctor_get(v___x_687_, 8);
v_snapshotTasks_696_ = lean_ctor_get(v___x_687_, 9);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; 
v_unused_751_ = lean_ctor_get(v___x_687_, 5);
lean_dec(v_unused_751_);
v___x_698_ = v___x_687_;
v_isShared_699_ = v_isSharedCheck_750_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_snapshotTasks_696_);
lean_inc(v_infoState_695_);
lean_inc(v_messages_694_);
lean_inc(v_recordedDeps_693_);
lean_inc(v_traceState_692_);
lean_inc(v_auxDeclNGen_691_);
lean_inc(v_ngen_690_);
lean_inc(v_nextMacroScope_689_);
lean_inc(v_env_688_);
lean_dec(v___x_687_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_750_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_700_ = l_Lean_Environment_setExporting(v_env_688_, v_isExporting_674_);
v___x_701_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 5, v___x_701_);
lean_ctor_set(v___x_698_, 0, v___x_700_);
v___x_703_ = v___x_698_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_nextMacroScope_689_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v_ngen_690_);
lean_ctor_set(v_reuseFailAlloc_749_, 3, v_auxDeclNGen_691_);
lean_ctor_set(v_reuseFailAlloc_749_, 4, v_traceState_692_);
lean_ctor_set(v_reuseFailAlloc_749_, 5, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_749_, 6, v_recordedDeps_693_);
lean_ctor_set(v_reuseFailAlloc_749_, 7, v_messages_694_);
lean_ctor_set(v_reuseFailAlloc_749_, 8, v_infoState_695_);
lean_ctor_set(v_reuseFailAlloc_749_, 9, v_snapshotTasks_696_);
v___x_703_ = v_reuseFailAlloc_749_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v_mctx_706_; lean_object* v_zetaDeltaFVarIds_707_; lean_object* v_postponed_708_; lean_object* v_diag_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_747_; 
v___x_704_ = lean_st_ref_put(v___y_678_, v___x_703_);
v___x_705_ = lean_st_ref_take(v___y_676_);
v_mctx_706_ = lean_ctor_get(v___x_705_, 0);
v_zetaDeltaFVarIds_707_ = lean_ctor_get(v___x_705_, 2);
v_postponed_708_ = lean_ctor_get(v___x_705_, 3);
v_diag_709_ = lean_ctor_get(v___x_705_, 4);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; 
v_unused_748_ = lean_ctor_get(v___x_705_, 1);
lean_dec(v_unused_748_);
v___x_711_ = v___x_705_;
v_isShared_712_ = v_isSharedCheck_747_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_diag_709_);
lean_inc(v_postponed_708_);
lean_inc(v_zetaDeltaFVarIds_707_);
lean_inc(v_mctx_706_);
lean_dec(v___x_705_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_747_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_713_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 1, v___x_713_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_mctx_706_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_746_, 2, v_zetaDeltaFVarIds_707_);
lean_ctor_set(v_reuseFailAlloc_746_, 3, v_postponed_708_);
lean_ctor_set(v_reuseFailAlloc_746_, 4, v_diag_709_);
v___x_715_ = v_reuseFailAlloc_746_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_716_; lean_object* v_r_717_; 
v___x_716_ = lean_st_ref_put(v___y_676_, v___x_715_);
lean_inc(v___y_678_);
lean_inc_ref(v___y_677_);
lean_inc(v___y_676_);
lean_inc_ref(v___y_675_);
v_r_717_ = lean_apply_5(v_x_673_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, lean_box(0));
if (lean_obj_tag(v_r_717_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_734_; 
v_a_718_ = lean_ctor_get(v_r_717_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v_r_717_);
if (v_isSharedCheck_734_ == 0)
{
v___x_720_ = v_r_717_;
v_isShared_721_ = v_isSharedCheck_734_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v_r_717_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_734_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
lean_inc(v_a_718_);
if (v_isShared_721_ == 0)
{
lean_ctor_set_tag(v___x_720_, 1);
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_733_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
v___x_724_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0(v___y_678_, v_isExporting_685_, v___x_701_, v___y_676_, v___x_713_, v___x_723_);
lean_dec_ref(v___x_723_);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; 
v_unused_732_ = lean_ctor_get(v___x_724_, 0);
lean_dec(v_unused_732_);
v___x_726_ = v___x_724_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_dec(v___x_724_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 0, v_a_718_);
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_718_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
v_a_735_ = lean_ctor_get(v_r_717_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v_r_717_, 1);
v___x_736_ = lean_box(0);
v___x_737_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0(v___y_678_, v_isExporting_685_, v___x_701_, v___y_676_, v___x_713_, v___x_736_);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_744_ == 0)
{
lean_object* v_unused_745_; 
v_unused_745_ = lean_ctor_get(v___x_737_, 0);
lean_dec(v_unused_745_);
v___x_739_ = v___x_737_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_dec(v___x_737_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set_tag(v___x_739_, 1);
lean_ctor_set(v___x_739_, 0, v_a_735_);
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_735_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
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
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___boxed(lean_object* v_x_754_, lean_object* v_isExporting_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
uint8_t v_isExporting_boxed_761_; lean_object* v_res_762_; 
v_isExporting_boxed_761_ = lean_unbox(v_isExporting_755_);
v_res_762_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(v_x_754_, v_isExporting_boxed_761_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12(lean_object* v_00_u03b1_763_, lean_object* v_x_764_, uint8_t v_isExporting_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(v_x_764_, v_isExporting_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___boxed(lean_object* v_00_u03b1_772_, lean_object* v_x_773_, lean_object* v_isExporting_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
uint8_t v_isExporting_boxed_780_; lean_object* v_res_781_; 
v_isExporting_boxed_780_ = lean_unbox(v_isExporting_774_);
v_res_781_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12(v_00_u03b1_772_, v_x_773_, v_isExporting_boxed_780_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(lean_object* v_cidx_782_, uint8_t v___x_783_, uint8_t v___x_784_, uint8_t v___x_785_, lean_object* v_ys_786_, lean_object* v_x_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = l_Lean_mkRawNatLit(v_cidx_782_);
v___x_794_ = l_Lean_Meta_mkLambdaFVars(v_ys_786_, v___x_793_, v___x_783_, v___x_784_, v___x_783_, v___x_784_, v___x_785_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed(lean_object* v_cidx_795_, lean_object* v___x_796_, lean_object* v___x_797_, lean_object* v___x_798_, lean_object* v_ys_799_, lean_object* v_x_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
uint8_t v___x_20188__boxed_806_; uint8_t v___x_20189__boxed_807_; uint8_t v___x_20190__boxed_808_; lean_object* v_res_809_; 
v___x_20188__boxed_806_ = lean_unbox(v___x_796_);
v___x_20189__boxed_807_ = lean_unbox(v___x_797_);
v___x_20190__boxed_808_ = lean_unbox(v___x_798_);
v_res_809_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(v_cidx_795_, v___x_20188__boxed_806_, v___x_20189__boxed_807_, v___x_20190__boxed_808_, v_ys_799_, v_x_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec_ref(v_x_800_);
lean_dec_ref(v_ys_799_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(lean_object* v_msgData_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v___x_816_; lean_object* v_env_817_; lean_object* v___x_818_; lean_object* v_toCold_819_; lean_object* v_mctx_820_; lean_object* v_lctx_821_; lean_object* v_options_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_816_ = lean_st_ref_get(v___y_814_);
v_env_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc_ref(v_env_817_);
lean_dec(v___x_816_);
v___x_818_ = lean_st_ref_get(v___y_812_);
v_toCold_819_ = lean_ctor_get(v___y_813_, 0);
v_mctx_820_ = lean_ctor_get(v___x_818_, 0);
lean_inc_ref(v_mctx_820_);
lean_dec(v___x_818_);
v_lctx_821_ = lean_ctor_get(v___y_811_, 2);
v_options_822_ = lean_ctor_get(v_toCold_819_, 2);
lean_inc_ref(v_options_822_);
lean_inc_ref(v_lctx_821_);
v___x_823_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_823_, 0, v_env_817_);
lean_ctor_set(v___x_823_, 1, v_mctx_820_);
lean_ctor_set(v___x_823_, 2, v_lctx_821_);
lean_ctor_set(v___x_823_, 3, v_options_822_);
v___x_824_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
lean_ctor_set(v___x_824_, 1, v_msgData_810_);
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11___boxed(lean_object* v_msgData_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(v_msgData_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(lean_object* v_msg_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_ref_839_; lean_object* v___x_840_; lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_849_; 
v_ref_839_ = lean_ctor_get(v___y_836_, 2);
v___x_840_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(v_msg_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
v_a_841_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_849_ == 0)
{
v___x_843_ = v___x_840_;
v_isShared_844_ = v_isSharedCheck_849_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_840_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_849_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___x_847_; 
lean_inc(v_ref_839_);
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v_ref_839_);
lean_ctor_set(v___x_845_, 1, v_a_841_);
if (v_isShared_844_ == 0)
{
lean_ctor_set_tag(v___x_843_, 1);
lean_ctor_set(v___x_843_, 0, v___x_845_);
v___x_847_ = v___x_843_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg___boxed(lean_object* v_msg_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
return v_res_856_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0(void){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_instMonadEIO___redArg();
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(lean_object* v_msg_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v_toApplicative_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_931_; 
v___x_868_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0);
v___x_869_ = l_StateRefT_x27_instMonad___redArg(v___x_868_);
v_toApplicative_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_931_ == 0)
{
lean_object* v_unused_932_; 
v_unused_932_ = lean_ctor_get(v___x_869_, 1);
lean_dec(v_unused_932_);
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_931_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_toApplicative_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_931_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v_toFunctor_874_; lean_object* v_toSeq_875_; lean_object* v_toSeqLeft_876_; lean_object* v_toSeqRight_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_929_; 
v_toFunctor_874_ = lean_ctor_get(v_toApplicative_870_, 0);
v_toSeq_875_ = lean_ctor_get(v_toApplicative_870_, 2);
v_toSeqLeft_876_ = lean_ctor_get(v_toApplicative_870_, 3);
v_toSeqRight_877_ = lean_ctor_get(v_toApplicative_870_, 4);
v_isSharedCheck_929_ = !lean_is_exclusive(v_toApplicative_870_);
if (v_isSharedCheck_929_ == 0)
{
lean_object* v_unused_930_; 
v_unused_930_ = lean_ctor_get(v_toApplicative_870_, 1);
lean_dec(v_unused_930_);
v___x_879_ = v_toApplicative_870_;
v_isShared_880_ = v_isSharedCheck_929_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_toSeqRight_877_);
lean_inc(v_toSeqLeft_876_);
lean_inc(v_toSeq_875_);
lean_inc(v_toFunctor_874_);
lean_dec(v_toApplicative_870_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_929_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___f_881_; lean_object* v___f_882_; lean_object* v___f_883_; lean_object* v___f_884_; lean_object* v___x_885_; lean_object* v___f_886_; lean_object* v___f_887_; lean_object* v___f_888_; lean_object* v___x_890_; 
v___f_881_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__1));
v___f_882_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__2));
lean_inc_ref(v_toFunctor_874_);
v___f_883_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_883_, 0, v_toFunctor_874_);
v___f_884_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_884_, 0, v_toFunctor_874_);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___f_883_);
lean_ctor_set(v___x_885_, 1, v___f_884_);
v___f_886_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_886_, 0, v_toSeqRight_877_);
v___f_887_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_887_, 0, v_toSeqLeft_876_);
v___f_888_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_888_, 0, v_toSeq_875_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 4, v___f_886_);
lean_ctor_set(v___x_879_, 3, v___f_887_);
lean_ctor_set(v___x_879_, 2, v___f_888_);
lean_ctor_set(v___x_879_, 1, v___f_881_);
lean_ctor_set(v___x_879_, 0, v___x_885_);
v___x_890_ = v___x_879_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v___f_881_);
lean_ctor_set(v_reuseFailAlloc_928_, 2, v___f_888_);
lean_ctor_set(v_reuseFailAlloc_928_, 3, v___f_887_);
lean_ctor_set(v_reuseFailAlloc_928_, 4, v___f_886_);
v___x_890_ = v_reuseFailAlloc_928_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_892_; 
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 1, v___f_882_);
lean_ctor_set(v___x_872_, 0, v___x_890_);
v___x_892_ = v___x_872_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v___f_882_);
v___x_892_ = v_reuseFailAlloc_927_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_893_; lean_object* v_toApplicative_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_925_; 
v___x_893_ = l_StateRefT_x27_instMonad___redArg(v___x_892_);
v_toApplicative_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_925_ == 0)
{
lean_object* v_unused_926_; 
v_unused_926_ = lean_ctor_get(v___x_893_, 1);
lean_dec(v_unused_926_);
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_925_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_toApplicative_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_925_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_toFunctor_898_; lean_object* v_toSeq_899_; lean_object* v_toSeqLeft_900_; lean_object* v_toSeqRight_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_923_; 
v_toFunctor_898_ = lean_ctor_get(v_toApplicative_894_, 0);
v_toSeq_899_ = lean_ctor_get(v_toApplicative_894_, 2);
v_toSeqLeft_900_ = lean_ctor_get(v_toApplicative_894_, 3);
v_toSeqRight_901_ = lean_ctor_get(v_toApplicative_894_, 4);
v_isSharedCheck_923_ = !lean_is_exclusive(v_toApplicative_894_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; 
v_unused_924_ = lean_ctor_get(v_toApplicative_894_, 1);
lean_dec(v_unused_924_);
v___x_903_ = v_toApplicative_894_;
v_isShared_904_ = v_isSharedCheck_923_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_toSeqRight_901_);
lean_inc(v_toSeqLeft_900_);
lean_inc(v_toSeq_899_);
lean_inc(v_toFunctor_898_);
lean_dec(v_toApplicative_894_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_923_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___f_905_; lean_object* v___f_906_; lean_object* v___f_907_; lean_object* v___f_908_; lean_object* v___x_909_; lean_object* v___f_910_; lean_object* v___f_911_; lean_object* v___f_912_; lean_object* v___x_914_; 
v___f_905_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__3));
v___f_906_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__4));
lean_inc_ref(v_toFunctor_898_);
v___f_907_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_907_, 0, v_toFunctor_898_);
v___f_908_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_908_, 0, v_toFunctor_898_);
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v___f_907_);
lean_ctor_set(v___x_909_, 1, v___f_908_);
v___f_910_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_910_, 0, v_toSeqRight_901_);
v___f_911_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_911_, 0, v_toSeqLeft_900_);
v___f_912_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_912_, 0, v_toSeq_899_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 4, v___f_910_);
lean_ctor_set(v___x_903_, 3, v___f_911_);
lean_ctor_set(v___x_903_, 2, v___f_912_);
lean_ctor_set(v___x_903_, 1, v___f_905_);
lean_ctor_set(v___x_903_, 0, v___x_909_);
v___x_914_ = v___x_903_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_909_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v___f_905_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v___f_912_);
lean_ctor_set(v_reuseFailAlloc_922_, 3, v___f_911_);
lean_ctor_set(v_reuseFailAlloc_922_, 4, v___f_910_);
v___x_914_ = v_reuseFailAlloc_922_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
lean_object* v___x_916_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 1, v___f_906_);
lean_ctor_set(v___x_896_, 0, v___x_914_);
v___x_916_ = v___x_896_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v___f_906_);
v___x_916_ = v_reuseFailAlloc_921_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_16397__overap_919_; lean_object* v___x_920_; 
v___x_917_ = lean_box(0);
v___x_918_ = l_instInhabitedOfMonad___redArg(v___x_916_, v___x_917_);
v___x_16397__overap_919_ = lean_panic_fn_borrowed(v___x_918_, v_msg_862_);
lean_dec(v___x_918_);
lean_inc(v___y_866_);
lean_inc_ref(v___y_865_);
lean_inc(v___y_864_);
lean_inc_ref(v___y_863_);
v___x_920_ = lean_apply_5(v___x_16397__overap_919_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, lean_box(0));
return v___x_920_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___boxed(lean_object* v_msg_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(v_msg_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
return v_res_939_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__0));
v___x_942_ = l_Lean_stringToMessageData(v___x_941_);
return v___x_942_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__2));
v___x_945_ = l_Lean_stringToMessageData(v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_949_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6));
v___x_950_ = lean_unsigned_to_nat(11u);
v___x_951_ = lean_unsigned_to_nat(122u);
v___x_952_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__5));
v___x_953_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__4));
v___x_954_ = l_mkPanicMessageWithDecl(v___x_953_, v___x_952_, v___x_951_, v___x_950_, v___x_949_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(lean_object* v_constName_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_969_; lean_object* v_env_970_; uint8_t v___x_971_; lean_object* v___x_972_; 
v___x_969_ = lean_st_ref_get(v___y_959_);
v_env_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc_ref(v_env_970_);
lean_dec(v___x_969_);
v___x_971_ = 0;
lean_inc(v_constName_955_);
v___x_972_ = l_Lean_Environment_findAsync_x3f(v_env_970_, v_constName_955_, v___x_971_);
if (lean_obj_tag(v___x_972_) == 1)
{
lean_object* v_val_973_; uint8_t v_kind_974_; 
v_val_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_val_973_);
lean_dec_ref_known(v___x_972_, 1);
v_kind_974_ = lean_ctor_get_uint8(v_val_973_, sizeof(void*)*3);
if (v_kind_974_ == 6)
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_973_);
if (lean_obj_tag(v___x_975_) == 6)
{
lean_object* v_val_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec(v_constName_955_);
v_val_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_val_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set_tag(v___x_978_, 0);
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_val_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; 
lean_dec_ref(v___x_975_);
v___x_984_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7);
v___x_985_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(v___x_984_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_994_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_994_ == 0)
{
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_994_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_994_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
if (lean_obj_tag(v_a_986_) == 0)
{
lean_del_object(v___x_988_);
goto v___jp_961_;
}
else
{
lean_object* v_val_990_; lean_object* v___x_992_; 
lean_dec(v_constName_955_);
v_val_990_ = lean_ctor_get(v_a_986_, 0);
lean_inc(v_val_990_);
lean_dec_ref_known(v_a_986_, 1);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v_val_990_);
v___x_992_ = v___x_988_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_val_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_dec(v_constName_955_);
v_a_995_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_985_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_985_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
else
{
lean_dec(v_val_973_);
goto v___jp_961_;
}
}
else
{
lean_dec(v___x_972_);
goto v___jp_961_;
}
v___jp_961_:
{
lean_object* v___x_962_; uint8_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_962_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1);
v___x_963_ = 0;
v___x_964_ = l_Lean_MessageData_ofConstName(v_constName_955_, v___x_963_);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_962_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v___x_967_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
return v___x_968_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___boxed(lean_object* v_constName_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(v_constName_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(uint8_t v___x_1010_, lean_object* v___x_1011_, lean_object* v_as_x27_1012_, lean_object* v_b_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
if (lean_obj_tag(v_as_x27_1012_) == 0)
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v_b_1013_);
return v___x_1019_;
}
else
{
lean_object* v_head_1020_; lean_object* v_tail_1021_; uint8_t v___x_1022_; uint8_t v___x_1023_; lean_object* v___x_1024_; 
v_head_1020_ = lean_ctor_get(v_as_x27_1012_, 0);
v_tail_1021_ = lean_ctor_get(v_as_x27_1012_, 1);
v___x_1022_ = 0;
v___x_1023_ = 1;
lean_inc(v_head_1020_);
v___x_1024_ = l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(v_head_1020_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v_toConstantVal_1026_; lean_object* v_cidx_1027_; lean_object* v_numFields_1028_; lean_object* v_type_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___f_1033_; lean_object* v___x_1034_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v_toConstantVal_1026_ = lean_ctor_get(v_a_1025_, 0);
lean_inc_ref(v_toConstantVal_1026_);
v_cidx_1027_ = lean_ctor_get(v_a_1025_, 2);
lean_inc(v_cidx_1027_);
v_numFields_1028_ = lean_ctor_get(v_a_1025_, 4);
lean_inc(v_numFields_1028_);
lean_dec(v_a_1025_);
v_type_1029_ = lean_ctor_get(v_toConstantVal_1026_, 2);
lean_inc_ref(v_type_1029_);
lean_dec_ref(v_toConstantVal_1026_);
v___x_1030_ = lean_box(v___x_1022_);
v___x_1031_ = lean_box(v___x_1010_);
v___x_1032_ = lean_box(v___x_1023_);
v___f_1033_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1033_, 0, v_cidx_1027_);
lean_closure_set(v___f_1033_, 1, v___x_1030_);
lean_closure_set(v___f_1033_, 2, v___x_1031_);
lean_closure_set(v___f_1033_, 3, v___x_1032_);
v___x_1034_ = l_Lean_Meta_instantiateForall(v_type_1029_, v___x_1011_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1046_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1037_ = v___x_1034_;
v_isShared_1038_ = v_isSharedCheck_1046_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1046_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 1);
lean_ctor_set(v___x_1037_, 0, v_numFields_1028_);
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_numFields_1028_);
v___x_1040_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_a_1035_, v___x_1040_, v___f_1033_, v___x_1022_, v___x_1022_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1043_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_a_1042_);
lean_dec_ref_known(v___x_1041_, 1);
v___x_1043_ = l_Lean_Expr_app___override(v_b_1013_, v_a_1042_);
v_as_x27_1012_ = v_tail_1021_;
v_b_1013_ = v___x_1043_;
goto _start;
}
else
{
lean_dec_ref(v_b_1013_);
return v___x_1041_;
}
}
}
}
else
{
lean_dec_ref(v___f_1033_);
lean_dec(v_numFields_1028_);
lean_dec_ref(v_b_1013_);
return v___x_1034_;
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec_ref(v_b_1013_);
v_a_1047_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1024_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1024_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___boxed(lean_object* v___x_1055_, lean_object* v___x_1056_, lean_object* v_as_x27_1057_, lean_object* v_b_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
uint8_t v___x_20560__boxed_1064_; lean_object* v_res_1065_; 
v___x_20560__boxed_1064_ = lean_unbox(v___x_1055_);
v_res_1065_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_20560__boxed_1064_, v___x_1056_, v_as_x27_1057_, v_b_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v_as_x27_1057_);
lean_dec_ref(v___x_1056_);
return v_res_1065_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_box(0);
v___x_1067_ = l_Lean_Level_succ___override(v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0(lean_object* v_xs_1068_, uint8_t v___x_1069_, uint8_t v___x_1070_, uint8_t v___x_1071_, lean_object* v_val_1072_, lean_object* v___x_1073_, lean_object* v___x_1074_, lean_object* v___x_1075_, lean_object* v___x_1076_, lean_object* v___x_1077_, lean_object* v_ctors_1078_, lean_object* v___x_1079_, lean_object* v_x_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_value_1087_; lean_object* v___x_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1090_ = l_Lean_InductiveVal_numCtors(v_val_1072_);
v___x_1091_ = lean_unsigned_to_nat(1u);
v___x_1092_ = lean_nat_dec_eq(v___x_1090_, v___x_1091_);
lean_dec(v___x_1090_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
lean_dec(v___x_1079_);
lean_inc_ref(v_x_1080_);
lean_inc_ref(v___x_1073_);
v___x_1093_ = lean_array_push(v___x_1073_, v_x_1080_);
v___x_1094_ = l_Lean_Meta_mkLambdaFVars(v___x_1093_, v___x_1074_, v___x_1069_, v___x_1070_, v___x_1069_, v___x_1070_, v___x_1071_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec_ref(v___x_1093_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___x_1094_, 1);
v___x_1096_ = lean_obj_once(&l_Lean_mkCtorIdx___lam__0___closed__0, &l_Lean_mkCtorIdx___lam__0___closed__0_once, _init_l_Lean_mkCtorIdx___lam__0___closed__0);
v___x_1097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
lean_ctor_set(v___x_1097_, 1, v___x_1075_);
v___x_1098_ = l_Lean_mkConst(v___x_1076_, v___x_1097_);
v___x_1099_ = l_Lean_mkAppN(v___x_1098_, v___x_1077_);
v___x_1100_ = l_Lean_Expr_app___override(v___x_1099_, v_a_1095_);
v___x_1101_ = l_Lean_mkAppN(v___x_1100_, v___x_1073_);
lean_dec_ref(v___x_1073_);
lean_inc_ref(v_x_1080_);
v___x_1102_ = l_Lean_Expr_app___override(v___x_1101_, v_x_1080_);
v___x_1103_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_1070_, v___x_1077_, v_ctors_1078_, v___x_1102_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v___x_1103_, 1);
v_value_1087_ = v_a_1104_;
goto v___jp_1086_;
}
else
{
lean_dec_ref(v_x_1080_);
lean_dec_ref(v_xs_1068_);
return v___x_1103_;
}
}
else
{
lean_dec_ref(v_x_1080_);
lean_dec(v___x_1076_);
lean_dec(v___x_1075_);
lean_dec_ref(v___x_1073_);
lean_dec_ref(v_xs_1068_);
return v___x_1094_;
}
}
else
{
lean_object* v___x_1105_; 
lean_dec(v___x_1076_);
lean_dec(v___x_1075_);
lean_dec_ref(v___x_1074_);
lean_dec_ref(v___x_1073_);
v___x_1105_ = l_Lean_mkRawNatLit(v___x_1079_);
v_value_1087_ = v___x_1105_;
goto v___jp_1086_;
}
v___jp_1086_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = lean_array_push(v_xs_1068_, v_x_1080_);
v___x_1089_ = l_Lean_Meta_mkLambdaFVars(v___x_1088_, v_value_1087_, v___x_1069_, v___x_1070_, v___x_1069_, v___x_1070_, v___x_1071_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec_ref(v___x_1088_);
return v___x_1089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0___boxed(lean_object** _args){
lean_object* v_xs_1106_ = _args[0];
lean_object* v___x_1107_ = _args[1];
lean_object* v___x_1108_ = _args[2];
lean_object* v___x_1109_ = _args[3];
lean_object* v_val_1110_ = _args[4];
lean_object* v___x_1111_ = _args[5];
lean_object* v___x_1112_ = _args[6];
lean_object* v___x_1113_ = _args[7];
lean_object* v___x_1114_ = _args[8];
lean_object* v___x_1115_ = _args[9];
lean_object* v_ctors_1116_ = _args[10];
lean_object* v___x_1117_ = _args[11];
lean_object* v_x_1118_ = _args[12];
lean_object* v___y_1119_ = _args[13];
lean_object* v___y_1120_ = _args[14];
lean_object* v___y_1121_ = _args[15];
lean_object* v___y_1122_ = _args[16];
lean_object* v___y_1123_ = _args[17];
_start:
{
uint8_t v___x_20651__boxed_1124_; uint8_t v___x_20652__boxed_1125_; uint8_t v___x_20653__boxed_1126_; lean_object* v_res_1127_; 
v___x_20651__boxed_1124_ = lean_unbox(v___x_1107_);
v___x_20652__boxed_1125_ = lean_unbox(v___x_1108_);
v___x_20653__boxed_1126_ = lean_unbox(v___x_1109_);
v_res_1127_ = l_Lean_mkCtorIdx___lam__0(v_xs_1106_, v___x_20651__boxed_1124_, v___x_20652__boxed_1125_, v___x_20653__boxed_1126_, v_val_1110_, v___x_1111_, v___x_1112_, v___x_1113_, v___x_1114_, v___x_1115_, v_ctors_1116_, v___x_1117_, v_x_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v_ctors_1116_);
lean_dec_ref(v___x_1115_);
lean_dec_ref(v_val_1110_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(lean_object* v_k_1128_, lean_object* v_b_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v___x_1135_; 
lean_inc(v___y_1133_);
lean_inc_ref(v___y_1132_);
lean_inc(v___y_1131_);
lean_inc_ref(v___y_1130_);
v___x_1135_ = lean_apply_6(v_k_1128_, v_b_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, lean_box(0));
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(lean_object* v_k_1136_, lean_object* v_b_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(v_k_1136_, v_b_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(lean_object* v_name_1144_, uint8_t v_bi_1145_, lean_object* v_type_1146_, lean_object* v_k_1147_, uint8_t v_kind_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v___f_1154_; lean_object* v___x_1155_; 
v___f_1154_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1154_, 0, v_k_1147_);
v___x_1155_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1144_, v_bi_1145_, v_type_1146_, v___f_1154_, v_kind_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1155_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1155_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
v_a_1164_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1155_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1155_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___boxed(lean_object* v_name_1172_, lean_object* v_bi_1173_, lean_object* v_type_1174_, lean_object* v_k_1175_, lean_object* v_kind_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
uint8_t v_bi_boxed_1182_; uint8_t v_kind_boxed_1183_; lean_object* v_res_1184_; 
v_bi_boxed_1182_ = lean_unbox(v_bi_1173_);
v_kind_boxed_1183_ = lean_unbox(v_kind_1176_);
v_res_1184_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_1172_, v_bi_boxed_1182_, v_type_1174_, v_k_1175_, v_kind_boxed_1183_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(lean_object* v_name_1185_, lean_object* v_type_1186_, lean_object* v_k_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
uint8_t v___x_1193_; uint8_t v___x_1194_; lean_object* v___x_1195_; 
v___x_1193_ = 0;
v___x_1194_ = 0;
v___x_1195_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_1185_, v___x_1193_, v_type_1186_, v_k_1187_, v___x_1194_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg___boxed(lean_object* v_name_1196_, lean_object* v_type_1197_, lean_object* v_k_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v_name_1196_, v_type_1197_, v_k_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(lean_object* v_env_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___x_1209_; lean_object* v_nextMacroScope_1210_; lean_object* v_ngen_1211_; lean_object* v_auxDeclNGen_1212_; lean_object* v_traceState_1213_; lean_object* v_recordedDeps_1214_; lean_object* v_messages_1215_; lean_object* v_infoState_1216_; lean_object* v_snapshotTasks_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1243_; 
v___x_1209_ = lean_st_ref_take(v___y_1207_);
v_nextMacroScope_1210_ = lean_ctor_get(v___x_1209_, 1);
v_ngen_1211_ = lean_ctor_get(v___x_1209_, 2);
v_auxDeclNGen_1212_ = lean_ctor_get(v___x_1209_, 3);
v_traceState_1213_ = lean_ctor_get(v___x_1209_, 4);
v_recordedDeps_1214_ = lean_ctor_get(v___x_1209_, 6);
v_messages_1215_ = lean_ctor_get(v___x_1209_, 7);
v_infoState_1216_ = lean_ctor_get(v___x_1209_, 8);
v_snapshotTasks_1217_ = lean_ctor_get(v___x_1209_, 9);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; lean_object* v_unused_1245_; 
v_unused_1244_ = lean_ctor_get(v___x_1209_, 5);
lean_dec(v_unused_1244_);
v_unused_1245_ = lean_ctor_get(v___x_1209_, 0);
lean_dec(v_unused_1245_);
v___x_1219_ = v___x_1209_;
v_isShared_1220_ = v_isSharedCheck_1243_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_snapshotTasks_1217_);
lean_inc(v_infoState_1216_);
lean_inc(v_messages_1215_);
lean_inc(v_recordedDeps_1214_);
lean_inc(v_traceState_1213_);
lean_inc(v_auxDeclNGen_1212_);
lean_inc(v_ngen_1211_);
lean_inc(v_nextMacroScope_1210_);
lean_dec(v___x_1209_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1243_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1221_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 5, v___x_1221_);
lean_ctor_set(v___x_1219_, 0, v_env_1205_);
v___x_1223_ = v___x_1219_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_env_1205_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_nextMacroScope_1210_);
lean_ctor_set(v_reuseFailAlloc_1242_, 2, v_ngen_1211_);
lean_ctor_set(v_reuseFailAlloc_1242_, 3, v_auxDeclNGen_1212_);
lean_ctor_set(v_reuseFailAlloc_1242_, 4, v_traceState_1213_);
lean_ctor_set(v_reuseFailAlloc_1242_, 5, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1242_, 6, v_recordedDeps_1214_);
lean_ctor_set(v_reuseFailAlloc_1242_, 7, v_messages_1215_);
lean_ctor_set(v_reuseFailAlloc_1242_, 8, v_infoState_1216_);
lean_ctor_set(v_reuseFailAlloc_1242_, 9, v_snapshotTasks_1217_);
v___x_1223_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v_mctx_1226_; lean_object* v_zetaDeltaFVarIds_1227_; lean_object* v_postponed_1228_; lean_object* v_diag_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1240_; 
v___x_1224_ = lean_st_ref_put(v___y_1207_, v___x_1223_);
v___x_1225_ = lean_st_ref_take(v___y_1206_);
v_mctx_1226_ = lean_ctor_get(v___x_1225_, 0);
v_zetaDeltaFVarIds_1227_ = lean_ctor_get(v___x_1225_, 2);
v_postponed_1228_ = lean_ctor_get(v___x_1225_, 3);
v_diag_1229_ = lean_ctor_get(v___x_1225_, 4);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1240_ == 0)
{
lean_object* v_unused_1241_; 
v_unused_1241_ = lean_ctor_get(v___x_1225_, 1);
lean_dec(v_unused_1241_);
v___x_1231_ = v___x_1225_;
v_isShared_1232_ = v_isSharedCheck_1240_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_diag_1229_);
lean_inc(v_postponed_1228_);
lean_inc(v_zetaDeltaFVarIds_1227_);
lean_inc(v_mctx_1226_);
lean_dec(v___x_1225_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1240_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1233_ = lean_box(0);
v___x_1234_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___x_1234_);
v___x_1236_ = v___x_1231_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_mctx_1226_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1239_, 2, v_zetaDeltaFVarIds_1227_);
lean_ctor_set(v_reuseFailAlloc_1239_, 3, v_postponed_1228_);
lean_ctor_set(v_reuseFailAlloc_1239_, 4, v_diag_1229_);
v___x_1236_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = lean_st_ref_put(v___y_1206_, v___x_1236_);
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1233_);
return v___x_1238_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg___boxed(lean_object* v_env_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(v_env_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec(v___y_1247_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9(lean_object* v_declName_1251_, lean_object* v_impName_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v___x_1258_; lean_object* v_env_1259_; lean_object* v___x_1260_; 
v___x_1258_ = lean_st_ref_get(v___y_1256_);
v_env_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc_ref(v_env_1259_);
lean_dec(v___x_1258_);
v___x_1260_ = l_Lean_Compiler_setImplementedBy(v_env_1259_, v_declName_1251_, v_impName_1252_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1270_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1270_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1270_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set_tag(v___x_1263_, 3);
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = l_Lean_MessageData_ofFormat(v___x_1266_);
v___x_1268_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v___x_1267_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
return v___x_1268_;
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1272_; 
v_a_1271_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1271_);
lean_dec_ref_known(v___x_1260_, 1);
v___x_1272_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(v_a_1271_, v___y_1254_, v___y_1256_);
return v___x_1272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9___boxed(lean_object* v_declName_1273_, lean_object* v_impName_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9(v_declName_1273_, v_impName_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1(lean_object* v___x_1284_, lean_object* v___x_1285_, lean_object* v_xs_1286_, uint8_t v___x_1287_, uint8_t v___x_1288_, lean_object* v_val_1289_, lean_object* v___x_1290_, lean_object* v___x_1291_, lean_object* v___x_1292_, lean_object* v___x_1293_, lean_object* v_ctors_1294_, lean_object* v___x_1295_, lean_object* v___x_1296_, lean_object* v_levelParams_1297_, lean_object* v_indName_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v___x_1304_; 
lean_inc_ref(v___x_1285_);
lean_inc_ref(v___x_1284_);
v___x_1304_ = l_Lean_mkArrow(v___x_1284_, v___x_1285_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; uint8_t v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___f_1310_; lean_object* v___x_1311_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1304_, 1);
v___x_1306_ = 1;
v___x_1307_ = lean_box(v___x_1287_);
v___x_1308_ = lean_box(v___x_1288_);
v___x_1309_ = lean_box(v___x_1306_);
lean_inc_ref(v_val_1289_);
lean_inc_ref(v_xs_1286_);
v___f_1310_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1310_, 0, v_xs_1286_);
lean_closure_set(v___f_1310_, 1, v___x_1307_);
lean_closure_set(v___f_1310_, 2, v___x_1308_);
lean_closure_set(v___f_1310_, 3, v___x_1309_);
lean_closure_set(v___f_1310_, 4, v_val_1289_);
lean_closure_set(v___f_1310_, 5, v___x_1290_);
lean_closure_set(v___f_1310_, 6, v___x_1285_);
lean_closure_set(v___f_1310_, 7, v___x_1291_);
lean_closure_set(v___f_1310_, 8, v___x_1292_);
lean_closure_set(v___f_1310_, 9, v___x_1293_);
lean_closure_set(v___f_1310_, 10, v_ctors_1294_);
lean_closure_set(v___f_1310_, 11, v___x_1295_);
v___x_1311_ = l_Lean_Meta_mkForallFVars(v_xs_1286_, v_a_1305_, v___x_1287_, v___x_1288_, v___x_1288_, v___x_1306_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
lean_dec_ref(v_xs_1286_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref_known(v___x_1311_, 1);
v___x_1313_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__1___closed__1));
v___x_1314_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v___x_1313_, v___x_1284_, v___f_1310_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1316_; lean_object* v_env_1317_; uint32_t v___x_1318_; lean_object* v___x_1319_; uint32_t v___x_1320_; uint32_t v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1465_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc_n(v_a_1315_, 2);
lean_dec_ref_known(v___x_1314_, 1);
v___x_1316_ = lean_st_ref_get(v___y_1302_);
v_env_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc_ref(v_env_1317_);
lean_dec(v___x_1316_);
v___x_1318_ = l_Lean_getMaxHeight(v_env_1317_, v_a_1315_);
v___x_1319_ = lean_unsigned_to_nat(1u);
v___x_1320_ = 1;
v___x_1321_ = lean_uint32_add(v___x_1318_, v___x_1320_);
v___x_1322_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_1322_, 0, v___x_1321_);
lean_inc(v_a_1312_);
lean_inc(v_levelParams_1297_);
lean_inc(v___x_1296_);
v___x_1323_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v___x_1296_, v_levelParams_1297_, v_a_1312_, v_a_1315_, v___x_1322_, v___y_1302_);
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1326_ = v___x_1323_;
v_isShared_1327_ = v_isSharedCheck_1465_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1323_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1465_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
lean_ctor_set_tag(v___x_1326_, 1);
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___x_1356_; 
lean_inc_ref(v___x_1329_);
v___x_1356_ = l_Lean_addDecl(v___x_1329_, v___x_1287_, v___y_1301_, v___y_1302_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v___x_1357_; lean_object* v_env_1358_; lean_object* v_nextMacroScope_1359_; lean_object* v_ngen_1360_; lean_object* v_auxDeclNGen_1361_; lean_object* v_traceState_1362_; lean_object* v_recordedDeps_1363_; lean_object* v_messages_1364_; lean_object* v_infoState_1365_; lean_object* v_snapshotTasks_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1462_; 
lean_dec_ref_known(v___x_1356_, 1);
v___x_1357_ = lean_st_ref_take(v___y_1302_);
v_env_1358_ = lean_ctor_get(v___x_1357_, 0);
v_nextMacroScope_1359_ = lean_ctor_get(v___x_1357_, 1);
v_ngen_1360_ = lean_ctor_get(v___x_1357_, 2);
v_auxDeclNGen_1361_ = lean_ctor_get(v___x_1357_, 3);
v_traceState_1362_ = lean_ctor_get(v___x_1357_, 4);
v_recordedDeps_1363_ = lean_ctor_get(v___x_1357_, 6);
v_messages_1364_ = lean_ctor_get(v___x_1357_, 7);
v_infoState_1365_ = lean_ctor_get(v___x_1357_, 8);
v_snapshotTasks_1366_ = lean_ctor_get(v___x_1357_, 9);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; 
v_unused_1463_ = lean_ctor_get(v___x_1357_, 5);
lean_dec(v_unused_1463_);
v___x_1368_ = v___x_1357_;
v_isShared_1369_ = v_isSharedCheck_1462_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_snapshotTasks_1366_);
lean_inc(v_infoState_1365_);
lean_inc(v_messages_1364_);
lean_inc(v_recordedDeps_1363_);
lean_inc(v_traceState_1362_);
lean_inc(v_auxDeclNGen_1361_);
lean_inc(v_ngen_1360_);
lean_inc(v_nextMacroScope_1359_);
lean_inc(v_env_1358_);
lean_dec(v___x_1357_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1462_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
lean_inc(v___x_1296_);
v___x_1370_ = l_Lean_Meta_addToCompletionBlackList(v_env_1358_, v___x_1296_);
v___x_1371_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 5, v___x_1371_);
lean_ctor_set(v___x_1368_, 0, v___x_1370_);
v___x_1373_ = v___x_1368_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_nextMacroScope_1359_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_ngen_1360_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v_auxDeclNGen_1361_);
lean_ctor_set(v_reuseFailAlloc_1461_, 4, v_traceState_1362_);
lean_ctor_set(v_reuseFailAlloc_1461_, 5, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1461_, 6, v_recordedDeps_1363_);
lean_ctor_set(v_reuseFailAlloc_1461_, 7, v_messages_1364_);
lean_ctor_set(v_reuseFailAlloc_1461_, 8, v_infoState_1365_);
lean_ctor_set(v_reuseFailAlloc_1461_, 9, v_snapshotTasks_1366_);
v___x_1373_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v_mctx_1376_; lean_object* v_zetaDeltaFVarIds_1377_; lean_object* v_postponed_1378_; lean_object* v_diag_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1459_; 
v___x_1374_ = lean_st_ref_put(v___y_1302_, v___x_1373_);
v___x_1375_ = lean_st_ref_take(v___y_1300_);
v_mctx_1376_ = lean_ctor_get(v___x_1375_, 0);
v_zetaDeltaFVarIds_1377_ = lean_ctor_get(v___x_1375_, 2);
v_postponed_1378_ = lean_ctor_get(v___x_1375_, 3);
v_diag_1379_ = lean_ctor_get(v___x_1375_, 4);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1459_ == 0)
{
lean_object* v_unused_1460_; 
v_unused_1460_ = lean_ctor_get(v___x_1375_, 1);
lean_dec(v_unused_1460_);
v___x_1381_ = v___x_1375_;
v_isShared_1382_ = v_isSharedCheck_1459_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_diag_1379_);
lean_inc(v_postponed_1378_);
lean_inc(v_zetaDeltaFVarIds_1377_);
lean_inc(v_mctx_1376_);
lean_dec(v___x_1375_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1459_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1383_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 1, v___x_1383_);
v___x_1385_ = v___x_1381_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_mctx_1376_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1458_, 2, v_zetaDeltaFVarIds_1377_);
lean_ctor_set(v_reuseFailAlloc_1458_, 3, v_postponed_1378_);
lean_ctor_set(v_reuseFailAlloc_1458_, 4, v_diag_1379_);
v___x_1385_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v_env_1388_; lean_object* v_nextMacroScope_1389_; lean_object* v_ngen_1390_; lean_object* v_auxDeclNGen_1391_; lean_object* v_traceState_1392_; lean_object* v_recordedDeps_1393_; lean_object* v_messages_1394_; lean_object* v_infoState_1395_; lean_object* v_snapshotTasks_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1456_; 
v___x_1386_ = lean_st_ref_put(v___y_1300_, v___x_1385_);
v___x_1387_ = lean_st_ref_take(v___y_1302_);
v_env_1388_ = lean_ctor_get(v___x_1387_, 0);
v_nextMacroScope_1389_ = lean_ctor_get(v___x_1387_, 1);
v_ngen_1390_ = lean_ctor_get(v___x_1387_, 2);
v_auxDeclNGen_1391_ = lean_ctor_get(v___x_1387_, 3);
v_traceState_1392_ = lean_ctor_get(v___x_1387_, 4);
v_recordedDeps_1393_ = lean_ctor_get(v___x_1387_, 6);
v_messages_1394_ = lean_ctor_get(v___x_1387_, 7);
v_infoState_1395_ = lean_ctor_get(v___x_1387_, 8);
v_snapshotTasks_1396_ = lean_ctor_get(v___x_1387_, 9);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; 
v_unused_1457_ = lean_ctor_get(v___x_1387_, 5);
lean_dec(v_unused_1457_);
v___x_1398_ = v___x_1387_;
v_isShared_1399_ = v_isSharedCheck_1456_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_snapshotTasks_1396_);
lean_inc(v_infoState_1395_);
lean_inc(v_messages_1394_);
lean_inc(v_recordedDeps_1393_);
lean_inc(v_traceState_1392_);
lean_inc(v_auxDeclNGen_1391_);
lean_inc(v_ngen_1390_);
lean_inc(v_nextMacroScope_1389_);
lean_inc(v_env_1388_);
lean_dec(v___x_1387_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1456_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1402_; 
lean_inc(v___x_1296_);
v___x_1400_ = l_Lean_addProtected(v_env_1388_, v___x_1296_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 5, v___x_1371_);
lean_ctor_set(v___x_1398_, 0, v___x_1400_);
v___x_1402_ = v___x_1398_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1400_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_nextMacroScope_1389_);
lean_ctor_set(v_reuseFailAlloc_1455_, 2, v_ngen_1390_);
lean_ctor_set(v_reuseFailAlloc_1455_, 3, v_auxDeclNGen_1391_);
lean_ctor_set(v_reuseFailAlloc_1455_, 4, v_traceState_1392_);
lean_ctor_set(v_reuseFailAlloc_1455_, 5, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1455_, 6, v_recordedDeps_1393_);
lean_ctor_set(v_reuseFailAlloc_1455_, 7, v_messages_1394_);
lean_ctor_set(v_reuseFailAlloc_1455_, 8, v_infoState_1395_);
lean_ctor_set(v_reuseFailAlloc_1455_, 9, v_snapshotTasks_1396_);
v___x_1402_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v_mctx_1405_; lean_object* v_zetaDeltaFVarIds_1406_; lean_object* v_postponed_1407_; lean_object* v_diag_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1453_; 
v___x_1403_ = lean_st_ref_put(v___y_1302_, v___x_1402_);
v___x_1404_ = lean_st_ref_take(v___y_1300_);
v_mctx_1405_ = lean_ctor_get(v___x_1404_, 0);
v_zetaDeltaFVarIds_1406_ = lean_ctor_get(v___x_1404_, 2);
v_postponed_1407_ = lean_ctor_get(v___x_1404_, 3);
v_diag_1408_ = lean_ctor_get(v___x_1404_, 4);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; 
v_unused_1454_ = lean_ctor_get(v___x_1404_, 1);
lean_dec(v_unused_1454_);
v___x_1410_ = v___x_1404_;
v_isShared_1411_ = v_isSharedCheck_1453_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_diag_1408_);
lean_inc(v_postponed_1407_);
lean_inc(v_zetaDeltaFVarIds_1406_);
lean_inc(v_mctx_1405_);
lean_dec(v___x_1404_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1453_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 1, v___x_1383_);
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_mctx_1405_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_zetaDeltaFVarIds_1406_);
lean_ctor_set(v_reuseFailAlloc_1452_, 3, v_postponed_1407_);
lean_ctor_set(v_reuseFailAlloc_1452_, 4, v_diag_1408_);
v___x_1413_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v_env_1416_; uint8_t v___x_1417_; 
v___x_1414_ = lean_st_ref_put(v___y_1300_, v___x_1413_);
v___x_1415_ = lean_st_ref_get(v___y_1302_);
v_env_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc_ref(v_env_1416_);
lean_dec(v___x_1415_);
lean_inc(v_indName_1298_);
v___x_1417_ = l_Lean_isMarkedMeta(v_env_1416_, v_indName_1298_);
if (v___x_1417_ == 0)
{
v___y_1336_ = v___y_1299_;
v___y_1337_ = v___y_1300_;
v___y_1338_ = v___y_1301_;
v___y_1339_ = v___y_1302_;
goto v___jp_1335_;
}
else
{
lean_object* v___x_1418_; lean_object* v_env_1419_; lean_object* v_nextMacroScope_1420_; lean_object* v_ngen_1421_; lean_object* v_auxDeclNGen_1422_; lean_object* v_traceState_1423_; lean_object* v_recordedDeps_1424_; lean_object* v_messages_1425_; lean_object* v_infoState_1426_; lean_object* v_snapshotTasks_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1450_; 
v___x_1418_ = lean_st_ref_take(v___y_1302_);
v_env_1419_ = lean_ctor_get(v___x_1418_, 0);
v_nextMacroScope_1420_ = lean_ctor_get(v___x_1418_, 1);
v_ngen_1421_ = lean_ctor_get(v___x_1418_, 2);
v_auxDeclNGen_1422_ = lean_ctor_get(v___x_1418_, 3);
v_traceState_1423_ = lean_ctor_get(v___x_1418_, 4);
v_recordedDeps_1424_ = lean_ctor_get(v___x_1418_, 6);
v_messages_1425_ = lean_ctor_get(v___x_1418_, 7);
v_infoState_1426_ = lean_ctor_get(v___x_1418_, 8);
v_snapshotTasks_1427_ = lean_ctor_get(v___x_1418_, 9);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1450_ == 0)
{
lean_object* v_unused_1451_; 
v_unused_1451_ = lean_ctor_get(v___x_1418_, 5);
lean_dec(v_unused_1451_);
v___x_1429_ = v___x_1418_;
v_isShared_1430_ = v_isSharedCheck_1450_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_snapshotTasks_1427_);
lean_inc(v_infoState_1426_);
lean_inc(v_messages_1425_);
lean_inc(v_recordedDeps_1424_);
lean_inc(v_traceState_1423_);
lean_inc(v_auxDeclNGen_1422_);
lean_inc(v_ngen_1421_);
lean_inc(v_nextMacroScope_1420_);
lean_inc(v_env_1419_);
lean_dec(v___x_1418_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1450_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1431_; lean_object* v___x_1433_; 
lean_inc(v___x_1296_);
v___x_1431_ = l_Lean_markMeta(v_env_1419_, v___x_1296_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 5, v___x_1371_);
lean_ctor_set(v___x_1429_, 0, v___x_1431_);
v___x_1433_ = v___x_1429_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_nextMacroScope_1420_);
lean_ctor_set(v_reuseFailAlloc_1449_, 2, v_ngen_1421_);
lean_ctor_set(v_reuseFailAlloc_1449_, 3, v_auxDeclNGen_1422_);
lean_ctor_set(v_reuseFailAlloc_1449_, 4, v_traceState_1423_);
lean_ctor_set(v_reuseFailAlloc_1449_, 5, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1449_, 6, v_recordedDeps_1424_);
lean_ctor_set(v_reuseFailAlloc_1449_, 7, v_messages_1425_);
lean_ctor_set(v_reuseFailAlloc_1449_, 8, v_infoState_1426_);
lean_ctor_set(v_reuseFailAlloc_1449_, 9, v_snapshotTasks_1427_);
v___x_1433_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v_mctx_1436_; lean_object* v_zetaDeltaFVarIds_1437_; lean_object* v_postponed_1438_; lean_object* v_diag_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1447_; 
v___x_1434_ = lean_st_ref_put(v___y_1302_, v___x_1433_);
v___x_1435_ = lean_st_ref_take(v___y_1300_);
v_mctx_1436_ = lean_ctor_get(v___x_1435_, 0);
v_zetaDeltaFVarIds_1437_ = lean_ctor_get(v___x_1435_, 2);
v_postponed_1438_ = lean_ctor_get(v___x_1435_, 3);
v_diag_1439_ = lean_ctor_get(v___x_1435_, 4);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; 
v_unused_1448_ = lean_ctor_get(v___x_1435_, 1);
lean_dec(v_unused_1448_);
v___x_1441_ = v___x_1435_;
v_isShared_1442_ = v_isSharedCheck_1447_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_diag_1439_);
lean_inc(v_postponed_1438_);
lean_inc(v_zetaDeltaFVarIds_1437_);
lean_inc(v_mctx_1436_);
lean_dec(v___x_1435_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1447_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 1, v___x_1383_);
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_mctx_1436_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1446_, 2, v_zetaDeltaFVarIds_1437_);
lean_ctor_set(v_reuseFailAlloc_1446_, 3, v_postponed_1438_);
lean_ctor_set(v_reuseFailAlloc_1446_, 4, v_diag_1439_);
v___x_1444_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1445_; 
v___x_1445_ = lean_st_ref_put(v___y_1300_, v___x_1444_);
v___y_1336_ = v___y_1299_;
v___y_1337_ = v___y_1300_;
v___y_1338_ = v___y_1301_;
v___y_1339_ = v___y_1302_;
goto v___jp_1335_;
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
}
}
}
}
else
{
lean_dec_ref(v___x_1329_);
lean_dec(v_a_1312_);
lean_dec(v_indName_1298_);
lean_dec(v_levelParams_1297_);
lean_dec(v___x_1296_);
lean_dec_ref(v_val_1289_);
return v___x_1356_;
}
v___jp_1330_:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_compileDecl(v___x_1329_, v___x_1288_, v___y_1331_, v___y_1332_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v___x_1334_; 
lean_dec_ref_known(v___x_1333_, 1);
v___x_1334_ = l_Lean_enableRealizationsForConst(v___x_1296_, v___y_1331_, v___y_1332_);
return v___x_1334_;
}
else
{
lean_dec(v___x_1296_);
return v___x_1333_;
}
}
v___jp_1335_:
{
lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1340_ = l_Lean_InductiveVal_numCtors(v_val_1289_);
lean_dec_ref(v_val_1289_);
v___x_1341_ = lean_nat_dec_eq(v___x_1340_, v___x_1319_);
lean_dec(v___x_1340_);
if (v___x_1341_ == 0)
{
uint8_t v___x_1342_; 
v___x_1342_ = l_Lean_Compiler_LCNF_isRuntimeBuiltinType(v_indName_1298_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; 
v___x_1343_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl(v_indName_1298_, v_levelParams_1297_, v_a_1312_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1345_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1343_, 1);
lean_inc(v___x_1296_);
v___x_1345_ = l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9(v___x_1296_, v_a_1344_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_dec_ref_known(v___x_1345_, 1);
v___y_1331_ = v___y_1338_;
v___y_1332_ = v___y_1339_;
goto v___jp_1330_;
}
else
{
lean_dec_ref(v___x_1329_);
lean_dec(v___x_1296_);
return v___x_1345_;
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec_ref(v___x_1329_);
lean_dec(v___x_1296_);
v_a_1346_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1343_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1343_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
else
{
lean_dec(v_a_1312_);
lean_dec(v_indName_1298_);
lean_dec(v_levelParams_1297_);
v___y_1331_ = v___y_1338_;
v___y_1332_ = v___y_1339_;
goto v___jp_1330_;
}
}
else
{
uint8_t v___x_1354_; lean_object* v___x_1355_; 
lean_dec(v_a_1312_);
lean_dec(v_indName_1298_);
lean_dec(v_levelParams_1297_);
v___x_1354_ = 2;
lean_inc(v___x_1296_);
v___x_1355_ = l_Lean_Meta_setInlineAttribute(v___x_1296_, v___x_1354_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_dec_ref_known(v___x_1355_, 1);
v___y_1331_ = v___y_1338_;
v___y_1332_ = v___y_1339_;
goto v___jp_1330_;
}
else
{
lean_dec_ref(v___x_1329_);
lean_dec(v___x_1296_);
return v___x_1355_;
}
}
}
}
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_dec(v_a_1312_);
lean_dec(v_indName_1298_);
lean_dec(v_levelParams_1297_);
lean_dec(v___x_1296_);
lean_dec_ref(v_val_1289_);
v_a_1466_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1314_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1314_);
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
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_dec_ref(v___f_1310_);
lean_dec(v_indName_1298_);
lean_dec(v_levelParams_1297_);
lean_dec(v___x_1296_);
lean_dec_ref(v_val_1289_);
lean_dec_ref(v___x_1284_);
v_a_1474_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1311_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1311_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec(v_indName_1298_);
lean_dec(v_levelParams_1297_);
lean_dec(v___x_1296_);
lean_dec(v___x_1295_);
lean_dec(v_ctors_1294_);
lean_dec_ref(v___x_1293_);
lean_dec(v___x_1292_);
lean_dec(v___x_1291_);
lean_dec_ref(v___x_1290_);
lean_dec_ref(v_val_1289_);
lean_dec_ref(v_xs_1286_);
lean_dec_ref(v___x_1285_);
lean_dec_ref(v___x_1284_);
v_a_1482_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1304_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1304_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1___boxed(lean_object** _args){
lean_object* v___x_1490_ = _args[0];
lean_object* v___x_1491_ = _args[1];
lean_object* v_xs_1492_ = _args[2];
lean_object* v___x_1493_ = _args[3];
lean_object* v___x_1494_ = _args[4];
lean_object* v_val_1495_ = _args[5];
lean_object* v___x_1496_ = _args[6];
lean_object* v___x_1497_ = _args[7];
lean_object* v___x_1498_ = _args[8];
lean_object* v___x_1499_ = _args[9];
lean_object* v_ctors_1500_ = _args[10];
lean_object* v___x_1501_ = _args[11];
lean_object* v___x_1502_ = _args[12];
lean_object* v_levelParams_1503_ = _args[13];
lean_object* v_indName_1504_ = _args[14];
lean_object* v___y_1505_ = _args[15];
lean_object* v___y_1506_ = _args[16];
lean_object* v___y_1507_ = _args[17];
lean_object* v___y_1508_ = _args[18];
lean_object* v___y_1509_ = _args[19];
_start:
{
uint8_t v___x_20965__boxed_1510_; uint8_t v___x_20966__boxed_1511_; lean_object* v_res_1512_; 
v___x_20965__boxed_1510_ = lean_unbox(v___x_1493_);
v___x_20966__boxed_1511_ = lean_unbox(v___x_1494_);
v_res_1512_ = l_Lean_mkCtorIdx___lam__1(v___x_1490_, v___x_1491_, v_xs_1492_, v___x_20965__boxed_1510_, v___x_20966__boxed_1511_, v_val_1495_, v___x_1496_, v___x_1497_, v___x_1498_, v___x_1499_, v_ctors_1500_, v___x_1501_, v___x_1502_, v_levelParams_1503_, v_indName_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15(size_t v_sz_1513_, size_t v_i_1514_, lean_object* v_bs_1515_){
_start:
{
uint8_t v___x_1516_; 
v___x_1516_ = lean_usize_dec_lt(v_i_1514_, v_sz_1513_);
if (v___x_1516_ == 0)
{
return v_bs_1515_;
}
else
{
lean_object* v_v_1517_; lean_object* v___x_1518_; lean_object* v_bs_x27_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; size_t v___x_1524_; size_t v___x_1525_; lean_object* v___x_1526_; 
v_v_1517_ = lean_array_uget(v_bs_1515_, v_i_1514_);
v___x_1518_ = lean_unsigned_to_nat(0u);
v_bs_x27_1519_ = lean_array_uset(v_bs_1515_, v_i_1514_, v___x_1518_);
v___x_1520_ = l_Lean_Expr_fvarId_x21(v_v_1517_);
lean_dec(v_v_1517_);
v___x_1521_ = 1;
v___x_1522_ = lean_box(v___x_1521_);
v___x_1523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1520_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = ((size_t)1ULL);
v___x_1525_ = lean_usize_add(v_i_1514_, v___x_1524_);
v___x_1526_ = lean_array_uset(v_bs_x27_1519_, v_i_1514_, v___x_1523_);
v_i_1514_ = v___x_1525_;
v_bs_1515_ = v___x_1526_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15___boxed(lean_object* v_sz_1528_, lean_object* v_i_1529_, lean_object* v_bs_1530_){
_start:
{
size_t v_sz_boxed_1531_; size_t v_i_boxed_1532_; lean_object* v_res_1533_; 
v_sz_boxed_1531_ = lean_unbox_usize(v_sz_1528_);
lean_dec(v_sz_1528_);
v_i_boxed_1532_ = lean_unbox_usize(v_i_1529_);
lean_dec(v_i_1529_);
v_res_1533_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15(v_sz_boxed_1531_, v_i_boxed_1532_, v_bs_1530_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(lean_object* v_bs_1534_, lean_object* v_k_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1534_, v_k_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1541_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1541_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
v_a_1550_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1541_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1541_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg___boxed(lean_object* v_bs_1558_, lean_object* v_k_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(v_bs_1558_, v_k_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec_ref(v_bs_1558_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(lean_object* v_bs_1566_, lean_object* v_k_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
size_t v_sz_1573_; size_t v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v_sz_1573_ = lean_array_size(v_bs_1566_);
v___x_1574_ = ((size_t)0ULL);
v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15(v_sz_1573_, v___x_1574_, v_bs_1566_);
v___x_1576_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(v___x_1575_, v_k_1567_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
lean_dec_ref(v___x_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg___boxed(lean_object* v_bs_1577_, lean_object* v_k_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(v_bs_1577_, v_k_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2(lean_object* v_numParams_1588_, lean_object* v_indName_1589_, lean_object* v___x_1590_, lean_object* v___x_1591_, uint8_t v___x_1592_, uint8_t v___x_1593_, lean_object* v_val_1594_, lean_object* v___x_1595_, lean_object* v_ctors_1596_, lean_object* v___x_1597_, lean_object* v_levelParams_1598_, lean_object* v_xs_1599_, lean_object* v_x_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___f_1618_; lean_object* v___x_1619_; 
v___x_1606_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1588_);
lean_inc_ref_n(v_xs_1599_, 3);
v___x_1607_ = l_Array_toSubarray___redArg(v_xs_1599_, v___x_1606_, v_numParams_1588_);
v___x_1608_ = l_Subarray_copy___redArg(v___x_1607_);
v___x_1609_ = lean_array_get_size(v_xs_1599_);
v___x_1610_ = l_Array_toSubarray___redArg(v_xs_1599_, v_numParams_1588_, v___x_1609_);
v___x_1611_ = l_Subarray_copy___redArg(v___x_1610_);
lean_inc(v___x_1590_);
lean_inc(v_indName_1589_);
v___x_1612_ = l_Lean_mkConst(v_indName_1589_, v___x_1590_);
v___x_1613_ = l_Lean_mkAppN(v___x_1612_, v_xs_1599_);
v___x_1614_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__2___closed__1));
v___x_1615_ = l_Lean_mkConst(v___x_1614_, v___x_1591_);
v___x_1616_ = lean_box(v___x_1592_);
v___x_1617_ = lean_box(v___x_1593_);
v___f_1618_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__1___boxed), 20, 15);
lean_closure_set(v___f_1618_, 0, v___x_1613_);
lean_closure_set(v___f_1618_, 1, v___x_1615_);
lean_closure_set(v___f_1618_, 2, v_xs_1599_);
lean_closure_set(v___f_1618_, 3, v___x_1616_);
lean_closure_set(v___f_1618_, 4, v___x_1617_);
lean_closure_set(v___f_1618_, 5, v_val_1594_);
lean_closure_set(v___f_1618_, 6, v___x_1611_);
lean_closure_set(v___f_1618_, 7, v___x_1590_);
lean_closure_set(v___f_1618_, 8, v___x_1595_);
lean_closure_set(v___f_1618_, 9, v___x_1608_);
lean_closure_set(v___f_1618_, 10, v_ctors_1596_);
lean_closure_set(v___f_1618_, 11, v___x_1606_);
lean_closure_set(v___f_1618_, 12, v___x_1597_);
lean_closure_set(v___f_1618_, 13, v_levelParams_1598_);
lean_closure_set(v___f_1618_, 14, v_indName_1589_);
v___x_1619_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(v_xs_1599_, v___f_1618_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2___boxed(lean_object** _args){
lean_object* v_numParams_1620_ = _args[0];
lean_object* v_indName_1621_ = _args[1];
lean_object* v___x_1622_ = _args[2];
lean_object* v___x_1623_ = _args[3];
lean_object* v___x_1624_ = _args[4];
lean_object* v___x_1625_ = _args[5];
lean_object* v_val_1626_ = _args[6];
lean_object* v___x_1627_ = _args[7];
lean_object* v_ctors_1628_ = _args[8];
lean_object* v___x_1629_ = _args[9];
lean_object* v_levelParams_1630_ = _args[10];
lean_object* v_xs_1631_ = _args[11];
lean_object* v_x_1632_ = _args[12];
lean_object* v___y_1633_ = _args[13];
lean_object* v___y_1634_ = _args[14];
lean_object* v___y_1635_ = _args[15];
lean_object* v___y_1636_ = _args[16];
lean_object* v___y_1637_ = _args[17];
_start:
{
uint8_t v___x_21411__boxed_1638_; uint8_t v___x_21412__boxed_1639_; lean_object* v_res_1640_; 
v___x_21411__boxed_1638_ = lean_unbox(v___x_1624_);
v___x_21412__boxed_1639_ = lean_unbox(v___x_1625_);
v_res_1640_ = l_Lean_mkCtorIdx___lam__2(v_numParams_1620_, v_indName_1621_, v___x_1622_, v___x_1623_, v___x_21411__boxed_1638_, v___x_21412__boxed_1639_, v_val_1626_, v___x_1627_, v_ctors_1628_, v___x_1629_, v_levelParams_1630_, v_xs_1631_, v_x_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec_ref(v_x_1632_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
if (lean_obj_tag(v_a_1641_) == 0)
{
lean_object* v___x_1643_; 
v___x_1643_ = l_List_reverse___redArg(v_a_1642_);
return v___x_1643_;
}
else
{
lean_object* v_head_1644_; lean_object* v_tail_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1654_; 
v_head_1644_ = lean_ctor_get(v_a_1641_, 0);
v_tail_1645_ = lean_ctor_get(v_a_1641_, 1);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_a_1641_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1647_ = v_a_1641_;
v_isShared_1648_ = v_isSharedCheck_1654_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_tail_1645_);
lean_inc(v_head_1644_);
lean_dec(v_a_1641_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1654_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1649_; lean_object* v___x_1651_; 
v___x_1649_ = l_Lean_mkLevelParam(v_head_1644_);
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 1, v_a_1642_);
lean_ctor_set(v___x_1647_, 0, v___x_1649_);
v___x_1651_ = v___x_1647_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1649_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v_a_1642_);
v___x_1651_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
v_a_1641_ = v_tail_1645_;
v_a_1642_ = v___x_1651_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg(lean_object* v_ref_1655_, lean_object* v_msg_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v_toCold_1662_; lean_object* v_currRecDepth_1663_; lean_object* v_ref_1664_; uint16_t v_optionFlags_1665_; uint8_t v_suppressElabErrors_1666_; uint8_t v_isRecordingDeps_1667_; lean_object* v_ref_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v_toCold_1662_ = lean_ctor_get(v___y_1659_, 0);
v_currRecDepth_1663_ = lean_ctor_get(v___y_1659_, 1);
v_ref_1664_ = lean_ctor_get(v___y_1659_, 2);
v_optionFlags_1665_ = lean_ctor_get_uint16(v___y_1659_, sizeof(void*)*3);
v_suppressElabErrors_1666_ = lean_ctor_get_uint8(v___y_1659_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1667_ = lean_ctor_get_uint8(v___y_1659_, sizeof(void*)*3 + 3);
v_ref_1668_ = l_Lean_replaceRef(v_ref_1655_, v_ref_1664_);
lean_inc(v_currRecDepth_1663_);
lean_inc_ref(v_toCold_1662_);
v___x_1669_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1669_, 0, v_toCold_1662_);
lean_ctor_set(v___x_1669_, 1, v_currRecDepth_1663_);
lean_ctor_set(v___x_1669_, 2, v_ref_1668_);
lean_ctor_set_uint16(v___x_1669_, sizeof(void*)*3, v_optionFlags_1665_);
lean_ctor_set_uint8(v___x_1669_, sizeof(void*)*3 + 2, v_suppressElabErrors_1666_);
lean_ctor_set_uint8(v___x_1669_, sizeof(void*)*3 + 3, v_isRecordingDeps_1667_);
v___x_1670_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_1656_, v___y_1657_, v___y_1658_, v___x_1669_, v___y_1660_);
lean_dec_ref_known(v___x_1669_, 3);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg___boxed(lean_object* v_ref_1671_, lean_object* v_msg_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg(v_ref_1671_, v_msg_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v_ref_1671_);
return v_res_1678_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1);
v___x_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
return v___x_1680_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__1(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1681_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0);
v___x_1682_ = lean_unsigned_to_nat(0u);
v___x_1683_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
lean_ctor_set(v___x_1683_, 2, v___x_1682_);
lean_ctor_set(v___x_1683_, 3, v___x_1682_);
lean_ctor_set(v___x_1683_, 4, v___x_1681_);
lean_ctor_set(v___x_1683_, 5, v___x_1681_);
lean_ctor_set(v___x_1683_, 6, v___x_1681_);
lean_ctor_set(v___x_1683_, 7, v___x_1681_);
lean_ctor_set(v___x_1683_, 8, v___x_1681_);
lean_ctor_set(v___x_1683_, 9, v___x_1681_);
lean_ctor_set(v___x_1683_, 10, v___x_1681_);
return v___x_1683_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1684_ = lean_unsigned_to_nat(32u);
v___x_1685_ = lean_mk_empty_array_with_capacity(v___x_1684_);
v___x_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
return v___x_1686_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__3(void){
_start:
{
size_t v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1687_ = ((size_t)5ULL);
v___x_1688_ = lean_unsigned_to_nat(0u);
v___x_1689_ = lean_unsigned_to_nat(32u);
v___x_1690_ = lean_mk_empty_array_with_capacity(v___x_1689_);
v___x_1691_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__2);
v___x_1692_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
lean_ctor_set(v___x_1692_, 1, v___x_1690_);
lean_ctor_set(v___x_1692_, 2, v___x_1688_);
lean_ctor_set(v___x_1692_, 3, v___x_1688_);
lean_ctor_set_usize(v___x_1692_, 4, v___x_1687_);
return v___x_1692_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__4(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1693_ = lean_box(1);
v___x_1694_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__3);
v___x_1695_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0);
v___x_1696_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
lean_ctor_set(v___x_1696_, 1, v___x_1694_);
lean_ctor_set(v___x_1696_, 2, v___x_1693_);
return v___x_1696_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6(void){
_start:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__5));
v___x_1699_ = l_Lean_stringToMessageData(v___x_1698_);
return v___x_1699_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__8(void){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__7));
v___x_1702_ = l_Lean_stringToMessageData(v___x_1701_);
return v___x_1702_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__10(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__9));
v___x_1705_ = l_Lean_stringToMessageData(v___x_1704_);
return v___x_1705_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__12(void){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__11));
v___x_1708_ = l_Lean_stringToMessageData(v___x_1707_);
return v___x_1708_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__14(void){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__13));
v___x_1711_ = l_Lean_stringToMessageData(v___x_1710_);
return v___x_1711_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16(void){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__15));
v___x_1714_ = l_Lean_stringToMessageData(v___x_1713_);
return v___x_1714_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__17));
v___x_1717_ = l_Lean_stringToMessageData(v___x_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg(lean_object* v_msg_1718_, lean_object* v_declHint_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v_env_1724_; uint8_t v___x_1725_; 
v___x_1722_ = lean_box(0);
v___x_1723_ = lean_st_ref_get(v___y_1720_);
v_env_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc_ref(v_env_1724_);
lean_dec(v___x_1723_);
v___x_1725_ = l_Lean_Name_isAnonymous(v_declHint_1719_);
if (v___x_1725_ == 0)
{
uint8_t v_isExporting_1726_; 
v_isExporting_1726_ = lean_ctor_get_uint8(v_env_1724_, sizeof(void*)*8);
if (v_isExporting_1726_ == 0)
{
lean_object* v___x_1727_; 
lean_dec_ref(v_env_1724_);
lean_dec(v_declHint_1719_);
v___x_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1727_, 0, v_msg_1718_);
return v___x_1727_;
}
else
{
lean_object* v___x_1728_; uint8_t v___x_1729_; 
lean_inc_ref(v_env_1724_);
v___x_1728_ = l_Lean_Environment_setExporting(v_env_1724_, v___x_1725_);
lean_inc(v_declHint_1719_);
lean_inc_ref(v___x_1728_);
v___x_1729_ = l_Lean_Environment_contains(v___x_1728_, v_declHint_1719_, v_isExporting_1726_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; 
lean_dec_ref(v___x_1728_);
lean_dec_ref(v_env_1724_);
lean_dec(v_declHint_1719_);
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v_msg_1718_);
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v_c_1736_; lean_object* v___x_1737_; 
v___x_1731_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__1);
v___x_1732_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__4);
v___x_1733_ = l_Lean_Options_empty;
v___x_1734_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1728_);
lean_ctor_set(v___x_1734_, 1, v___x_1731_);
lean_ctor_set(v___x_1734_, 2, v___x_1732_);
lean_ctor_set(v___x_1734_, 3, v___x_1733_);
lean_inc(v_declHint_1719_);
v___x_1735_ = l_Lean_MessageData_ofConstName(v_declHint_1719_, v___x_1725_);
v_c_1736_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1736_, 0, v___x_1734_);
lean_ctor_set(v_c_1736_, 1, v___x_1735_);
v___x_1737_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1724_, v_declHint_1719_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_dec_ref(v_env_1724_);
lean_dec(v_declHint_1719_);
v___x_1738_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6);
v___x_1739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
lean_ctor_set(v___x_1739_, 1, v_c_1736_);
v___x_1740_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__8);
v___x_1741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1739_);
lean_ctor_set(v___x_1741_, 1, v___x_1740_);
v___x_1742_ = l_Lean_MessageData_note(v___x_1741_);
v___x_1743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1743_, 0, v_msg_1718_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
return v___x_1744_;
}
else
{
lean_object* v_val_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1779_; 
v_val_1745_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1747_ = v___x_1737_;
v_isShared_1748_ = v_isSharedCheck_1779_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_val_1745_);
lean_dec(v___x_1737_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1779_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v_mod_1751_; uint8_t v___x_1752_; 
v___x_1749_ = l_Lean_Environment_header(v_env_1724_);
lean_dec_ref(v_env_1724_);
v___x_1750_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1749_);
v_mod_1751_ = lean_array_get(v___x_1722_, v___x_1750_, v_val_1745_);
lean_dec(v_val_1745_);
lean_dec_ref(v___x_1750_);
v___x_1752_ = l_Lean_isPrivateName(v_declHint_1719_);
lean_dec(v_declHint_1719_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1753_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__10);
v___x_1754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
lean_ctor_set(v___x_1754_, 1, v_c_1736_);
v___x_1755_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__12);
v___x_1756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1754_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = l_Lean_MessageData_ofName(v_mod_1751_);
v___x_1758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1756_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__14);
v___x_1760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1758_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
v___x_1761_ = l_Lean_MessageData_note(v___x_1760_);
v___x_1762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1762_, 0, v_msg_1718_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set_tag(v___x_1747_, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1762_);
v___x_1764_ = v___x_1747_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1766_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6);
v___x_1767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
lean_ctor_set(v___x_1767_, 1, v_c_1736_);
v___x_1768_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16);
v___x_1769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
v___x_1770_ = l_Lean_MessageData_ofName(v_mod_1751_);
v___x_1771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1769_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v___x_1772_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18);
v___x_1773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1771_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v___x_1774_ = l_Lean_MessageData_note(v___x_1773_);
v___x_1775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1775_, 0, v_msg_1718_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set_tag(v___x_1747_, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1775_);
v___x_1777_ = v___x_1747_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1780_; 
lean_dec_ref(v_env_1724_);
lean_dec(v_declHint_1719_);
v___x_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1780_, 0, v_msg_1718_);
return v___x_1780_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___boxed(lean_object* v_msg_1781_, lean_object* v_declHint_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg(v_msg_1781_, v_declHint_1782_, v___y_1783_);
lean_dec(v___y_1783_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22(lean_object* v_msg_1786_, lean_object* v_declHint_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v___x_1793_; lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1803_; 
v___x_1793_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg(v_msg_1786_, v_declHint_1787_, v___y_1791_);
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1796_ = v___x_1793_;
v_isShared_1797_ = v_isSharedCheck_1803_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1793_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1803_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1801_; 
v___x_1798_ = l_Lean_unknownIdentifierMessageTag;
v___x_1799_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1798_);
lean_ctor_set(v___x_1799_, 1, v_a_1794_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 0, v___x_1799_);
v___x_1801_ = v___x_1796_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22___boxed(lean_object* v_msg_1804_, lean_object* v_declHint_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22(v_msg_1804_, v_declHint_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg(lean_object* v_ref_1812_, lean_object* v_msg_1813_, lean_object* v_declHint_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v___x_1820_; lean_object* v_a_1821_; lean_object* v___x_1822_; 
v___x_1820_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22(v_msg_1813_, v_declHint_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1821_);
lean_dec_ref(v___x_1820_);
v___x_1822_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg(v_ref_1812_, v_a_1821_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg___boxed(lean_object* v_ref_1823_, lean_object* v_msg_1824_, lean_object* v_declHint_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg(v_ref_1823_, v_msg_1824_, v_declHint_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v_ref_1823_);
return v_res_1831_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0));
v___x_1834_ = l_Lean_stringToMessageData(v___x_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(lean_object* v_ref_1835_, lean_object* v_constName_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v___x_1842_; uint8_t v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1842_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1);
v___x_1843_ = 0;
lean_inc(v_constName_1836_);
v___x_1844_ = l_Lean_MessageData_ofConstName(v_constName_1836_, v___x_1843_);
v___x_1845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1842_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___x_1846_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1);
v___x_1847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1845_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
v___x_1848_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg(v_ref_1835_, v___x_1847_, v_constName_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1849_, lean_object* v_constName_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1849_, v_constName_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v_ref_1849_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(lean_object* v_constName_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_ref_1863_; lean_object* v___x_1864_; 
v_ref_1863_ = lean_ctor_get(v___y_1860_, 2);
v___x_1864_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1863_, v_constName_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg___boxed(lean_object* v_constName_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(lean_object* v_constName_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v___x_1878_; lean_object* v_env_1879_; uint8_t v___x_1880_; lean_object* v___x_1881_; 
v___x_1878_ = lean_st_ref_get(v___y_1876_);
v_env_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc_ref(v_env_1879_);
lean_dec(v___x_1878_);
v___x_1880_ = 0;
lean_inc(v_constName_1872_);
v___x_1881_ = l_Lean_Environment_find_x3f(v_env_1879_, v_constName_1872_, v___x_1880_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
return v___x_1882_;
}
else
{
lean_object* v_val_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec(v_constName_1872_);
v_val_1883_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1881_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_val_1883_);
lean_dec(v___x_1881_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set_tag(v___x_1885_, 0);
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_val_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2___boxed(lean_object* v_constName_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_constName_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
return v_res_1897_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1900_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6));
v___x_1901_ = lean_unsigned_to_nat(62u);
v___x_1902_ = lean_unsigned_to_nat(83u);
v___x_1903_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__3___closed__1));
v___x_1904_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__3___closed__0));
v___x_1905_ = l_mkPanicMessageWithDecl(v___x_1904_, v___x_1903_, v___x_1902_, v___x_1901_, v___x_1900_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3(lean_object* v_indName_1906_, uint8_t v___x_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; uint8_t v___x_1915_; 
v___x_1913_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1910_);
v___x_1914_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_genCtorIdx;
v___x_1915_ = l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(v___x_1913_, v___x_1914_);
lean_dec_ref(v___x_1913_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
lean_dec(v_indName_1906_);
v___x_1916_ = lean_box(0);
v___x_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
return v___x_1917_;
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_2004_; 
lean_inc(v_indName_1906_);
v___x_1918_ = l_Lean_mkCtorIdxName(v_indName_1906_);
lean_inc(v___x_1918_);
v___x_1919_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v___x_1918_, v___x_1915_, v___y_1911_);
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_2004_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_2004_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
uint8_t v___x_1924_; 
v___x_1924_ = lean_unbox(v_a_1920_);
lean_dec(v_a_1920_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; 
lean_del_object(v___x_1922_);
lean_inc(v_indName_1906_);
v___x_1925_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_indName_1906_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___x_1925_, 1);
if (lean_obj_tag(v_a_1926_) == 5)
{
lean_object* v_val_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1989_; 
v_val_1927_ = lean_ctor_get(v_a_1926_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v_a_1926_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1929_ = v_a_1926_;
v_isShared_1930_ = v_isSharedCheck_1989_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_val_1927_);
lean_dec(v_a_1926_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1989_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v_toConstantVal_1931_; lean_object* v_numParams_1932_; lean_object* v_numIndices_1933_; lean_object* v_ctors_1934_; lean_object* v_levelParams_1935_; lean_object* v_type_1936_; lean_object* v___x_1937_; 
v_toConstantVal_1931_ = lean_ctor_get(v_val_1927_, 0);
v_numParams_1932_ = lean_ctor_get(v_val_1927_, 1);
lean_inc(v_numParams_1932_);
v_numIndices_1933_ = lean_ctor_get(v_val_1927_, 2);
lean_inc(v_numIndices_1933_);
v_ctors_1934_ = lean_ctor_get(v_val_1927_, 4);
lean_inc(v_ctors_1934_);
v_levelParams_1935_ = lean_ctor_get(v_toConstantVal_1931_, 1);
lean_inc(v_levelParams_1935_);
v_type_1936_ = lean_ctor_get(v_toConstantVal_1931_, 2);
lean_inc_ref_n(v_type_1936_, 2);
v___x_1937_ = l_Lean_Meta_isPropFormerType(v_type_1936_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1980_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1940_ = v___x_1937_;
v_isShared_1941_ = v_isSharedCheck_1980_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1980_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
uint8_t v___x_1942_; 
v___x_1942_ = lean_unbox(v_a_1938_);
lean_dec(v_a_1938_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_del_object(v___x_1940_);
lean_inc(v_indName_1906_);
v___x_1943_ = l_Lean_mkCasesOnName(v_indName_1906_);
lean_inc(v___x_1943_);
v___x_1944_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v___x_1943_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1967_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1947_ = v___x_1944_;
v_isShared_1948_ = v_isSharedCheck_1967_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1944_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1967_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v___x_1949_ = l_List_lengthTR___redArg(v_levelParams_1935_);
v___x_1950_ = l_Lean_ConstantInfo_levelParams(v_a_1945_);
lean_dec(v_a_1945_);
v___x_1951_ = l_List_lengthTR___redArg(v___x_1950_);
lean_dec(v___x_1950_);
v___x_1952_ = lean_nat_dec_lt(v___x_1949_, v___x_1951_);
lean_dec(v___x_1951_);
lean_dec(v___x_1949_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
lean_dec(v___x_1943_);
lean_dec_ref(v_type_1936_);
lean_dec(v_levelParams_1935_);
lean_dec(v_ctors_1934_);
lean_dec(v_numIndices_1933_);
lean_dec(v_numParams_1932_);
lean_del_object(v___x_1929_);
lean_dec_ref(v_val_1927_);
lean_dec(v___x_1918_);
lean_dec(v_indName_1906_);
v___x_1953_ = lean_box(0);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1953_);
v___x_1955_ = v___x_1947_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1953_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___f_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
lean_del_object(v___x_1947_);
v___x_1957_ = lean_box(0);
lean_inc(v_levelParams_1935_);
v___x_1958_ = l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(v_levelParams_1935_, v___x_1957_);
v___x_1959_ = lean_box(v___x_1907_);
v___x_1960_ = lean_box(v___x_1915_);
lean_inc(v_numParams_1932_);
v___f_1961_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__2___boxed), 18, 11);
lean_closure_set(v___f_1961_, 0, v_numParams_1932_);
lean_closure_set(v___f_1961_, 1, v_indName_1906_);
lean_closure_set(v___f_1961_, 2, v___x_1958_);
lean_closure_set(v___f_1961_, 3, v___x_1957_);
lean_closure_set(v___f_1961_, 4, v___x_1959_);
lean_closure_set(v___f_1961_, 5, v___x_1960_);
lean_closure_set(v___f_1961_, 6, v_val_1927_);
lean_closure_set(v___f_1961_, 7, v___x_1943_);
lean_closure_set(v___f_1961_, 8, v_ctors_1934_);
lean_closure_set(v___f_1961_, 9, v___x_1918_);
lean_closure_set(v___f_1961_, 10, v_levelParams_1935_);
v___x_1962_ = lean_nat_add(v_numParams_1932_, v_numIndices_1933_);
lean_dec(v_numIndices_1933_);
lean_dec(v_numParams_1932_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set_tag(v___x_1929_, 1);
lean_ctor_set(v___x_1929_, 0, v___x_1962_);
v___x_1964_ = v___x_1929_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1962_);
v___x_1964_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_1936_, v___x_1964_, v___f_1961_, v___x_1907_, v___x_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
return v___x_1965_;
}
}
}
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_dec(v___x_1943_);
lean_dec_ref(v_type_1936_);
lean_dec(v_levelParams_1935_);
lean_dec(v_ctors_1934_);
lean_dec(v_numIndices_1933_);
lean_dec(v_numParams_1932_);
lean_del_object(v___x_1929_);
lean_dec_ref(v_val_1927_);
lean_dec(v___x_1918_);
lean_dec(v_indName_1906_);
v_a_1968_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1944_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1944_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
else
{
lean_object* v___x_1976_; lean_object* v___x_1978_; 
lean_dec_ref(v_type_1936_);
lean_dec(v_levelParams_1935_);
lean_dec(v_ctors_1934_);
lean_dec(v_numIndices_1933_);
lean_dec(v_numParams_1932_);
lean_del_object(v___x_1929_);
lean_dec_ref(v_val_1927_);
lean_dec(v___x_1918_);
lean_dec(v_indName_1906_);
v___x_1976_ = lean_box(0);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1976_);
v___x_1978_ = v___x_1940_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_dec_ref(v_type_1936_);
lean_dec(v_levelParams_1935_);
lean_dec(v_ctors_1934_);
lean_dec(v_numIndices_1933_);
lean_dec(v_numParams_1932_);
lean_del_object(v___x_1929_);
lean_dec_ref(v_val_1927_);
lean_dec(v___x_1918_);
lean_dec(v_indName_1906_);
v_a_1981_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1937_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1937_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
else
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
lean_dec(v_a_1926_);
lean_dec(v___x_1918_);
lean_dec(v_indName_1906_);
v___x_1990_ = lean_obj_once(&l_Lean_mkCtorIdx___lam__3___closed__2, &l_Lean_mkCtorIdx___lam__3___closed__2_once, _init_l_Lean_mkCtorIdx___lam__3___closed__2);
v___x_1991_ = l_panic___at___00Lean_mkCtorIdx_spec__11(v___x_1990_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
return v___x_1991_;
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec(v___x_1918_);
lean_dec(v_indName_1906_);
v_a_1992_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1925_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1925_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
else
{
lean_object* v___x_2000_; lean_object* v___x_2002_; 
lean_dec(v___x_1918_);
lean_dec(v_indName_1906_);
v___x_2000_ = lean_box(0);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_2000_);
v___x_2002_ = v___x_1922_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3___boxed(lean_object* v_indName_2005_, lean_object* v___x_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
uint8_t v___x_21957__boxed_2012_; lean_object* v_res_2013_; 
v___x_21957__boxed_2012_ = lean_unbox(v___x_2006_);
v_res_2013_ = l_Lean_mkCtorIdx___lam__3(v_indName_2005_, v___x_21957__boxed_2012_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__4(lean_object* v___x_2014_, lean_object* v_e_2015_){
_start:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2016_ = l_Lean_indentD(v_e_2015_);
v___x_2017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2014_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5(lean_object* v___f_2018_, lean_object* v___f_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_){
_start:
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_Meta_mapErrorImp___redArg(v___f_2018_, v___f_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2025_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2025_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
v_a_2034_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2025_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2025_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5___boxed(lean_object* v___f_2042_, lean_object* v___f_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Lean_mkCtorIdx___lam__5(v___f_2042_, v___f_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
return v_res_2049_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___closed__1(void){
_start:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = ((lean_object*)(l_Lean_mkCtorIdx___closed__0));
v___x_2052_ = l_Lean_stringToMessageData(v___x_2051_);
return v___x_2052_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___closed__3(void){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = ((lean_object*)(l_Lean_mkCtorIdx___closed__2));
v___x_2055_ = l_Lean_stringToMessageData(v___x_2054_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx(lean_object* v_indName_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v___x_2062_; uint8_t v___x_2063_; lean_object* v___x_2064_; lean_object* v___f_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___f_2070_; lean_object* v___f_2071_; uint8_t v___x_2072_; 
v___x_2062_ = lean_obj_once(&l_Lean_mkCtorIdx___closed__1, &l_Lean_mkCtorIdx___closed__1_once, _init_l_Lean_mkCtorIdx___closed__1);
v___x_2063_ = 0;
v___x_2064_ = lean_box(v___x_2063_);
lean_inc_n(v_indName_2056_, 2);
v___f_2065_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__3___boxed), 7, 2);
lean_closure_set(v___f_2065_, 0, v_indName_2056_);
lean_closure_set(v___f_2065_, 1, v___x_2064_);
v___x_2066_ = l_Lean_MessageData_ofConstName(v_indName_2056_, v___x_2063_);
v___x_2067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2062_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
v___x_2068_ = lean_obj_once(&l_Lean_mkCtorIdx___closed__3, &l_Lean_mkCtorIdx___closed__3_once, _init_l_Lean_mkCtorIdx___closed__3);
v___x_2069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2067_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___f_2070_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__4), 2, 1);
lean_closure_set(v___f_2070_, 0, v___x_2069_);
v___f_2071_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__5___boxed), 7, 2);
lean_closure_set(v___f_2071_, 0, v___f_2065_);
lean_closure_set(v___f_2071_, 1, v___f_2070_);
v___x_2072_ = l_Lean_isPrivateName(v_indName_2056_);
lean_dec(v_indName_2056_);
if (v___x_2072_ == 0)
{
uint8_t v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = 1;
v___x_2074_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(v___f_2071_, v___x_2073_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_);
return v___x_2074_;
}
else
{
lean_object* v___x_2075_; 
v___x_2075_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(v___f_2071_, v___x_2063_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_);
return v___x_2075_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___boxed(lean_object* v_indName_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Lean_mkCtorIdx(v_indName_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_);
lean_dec(v_a_2080_);
lean_dec_ref(v_a_2079_);
lean_dec(v_a_2078_);
lean_dec_ref(v_a_2077_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(uint8_t v___x_2083_, lean_object* v___x_2084_, lean_object* v_as_2085_, lean_object* v_as_x27_2086_, lean_object* v_b_2087_, lean_object* v_a_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_2083_, v___x_2084_, v_as_x27_2086_, v_b_2087_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___boxed(lean_object* v___x_2095_, lean_object* v___x_2096_, lean_object* v_as_2097_, lean_object* v_as_x27_2098_, lean_object* v_b_2099_, lean_object* v_a_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
uint8_t v___x_22266__boxed_2106_; lean_object* v_res_2107_; 
v___x_22266__boxed_2106_ = lean_unbox(v___x_2095_);
v_res_2107_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(v___x_22266__boxed_2106_, v___x_2096_, v_as_2097_, v_as_x27_2098_, v_b_2099_, v_a_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v_as_x27_2098_);
lean_dec(v_as_2097_);
lean_dec_ref(v___x_2096_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10(lean_object* v_00_u03b1_2108_, lean_object* v_name_2109_, uint8_t v_bi_2110_, lean_object* v_type_2111_, lean_object* v_k_2112_, uint8_t v_kind_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_2109_, v_bi_2110_, v_type_2111_, v_k_2112_, v_kind_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2120_, lean_object* v_name_2121_, lean_object* v_bi_2122_, lean_object* v_type_2123_, lean_object* v_k_2124_, lean_object* v_kind_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
uint8_t v_bi_boxed_2131_; uint8_t v_kind_boxed_2132_; lean_object* v_res_2133_; 
v_bi_boxed_2131_ = lean_unbox(v_bi_2122_);
v_kind_boxed_2132_ = lean_unbox(v_kind_2125_);
v_res_2133_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10(v_00_u03b1_2120_, v_name_2121_, v_bi_boxed_2131_, v_type_2123_, v_k_2124_, v_kind_boxed_2132_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7(lean_object* v_00_u03b1_2134_, lean_object* v_name_2135_, lean_object* v_type_2136_, lean_object* v_k_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v_name_2135_, v_type_2136_, v_k_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___boxed(lean_object* v_00_u03b1_2144_, lean_object* v_name_2145_, lean_object* v_type_2146_, lean_object* v_k_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7(v_00_u03b1_2144_, v_name_2145_, v_type_2146_, v_k_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13(lean_object* v_env_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(v_env_2154_, v___y_2156_, v___y_2158_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___boxed(lean_object* v_env_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13(v_env_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16(lean_object* v_00_u03b1_2168_, lean_object* v_bs_2169_, lean_object* v_k_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(v_bs_2169_, v_k_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___boxed(lean_object* v_00_u03b1_2177_, lean_object* v_bs_2178_, lean_object* v_k_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16(v_00_u03b1_2177_, v_bs_2178_, v_k_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec_ref(v_bs_2178_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10(lean_object* v_00_u03b1_2186_, lean_object* v_bs_2187_, lean_object* v_k_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(v_bs_2187_, v_k_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___boxed(lean_object* v_00_u03b1_2195_, lean_object* v_bs_2196_, lean_object* v_k_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10(v_00_u03b1_2195_, v_bs_2196_, v_k_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(lean_object* v_00_u03b1_2204_, lean_object* v_constName_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2212_, lean_object* v_constName_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(v_00_u03b1_2212_, v_constName_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(lean_object* v_00_u03b1_2220_, lean_object* v_msg_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2228_, lean_object* v_msg_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(v_00_u03b1_2228_, v_msg_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7(lean_object* v_00_u03b1_2236_, lean_object* v_ref_2237_, lean_object* v_constName_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_2237_, v_constName_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___boxed(lean_object* v_00_u03b1_2245_, lean_object* v_ref_2246_, lean_object* v_constName_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7(v_00_u03b1_2245_, v_ref_2246_, v_constName_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v_ref_2246_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18(lean_object* v_00_u03b1_2254_, lean_object* v_ref_2255_, lean_object* v_msg_2256_, lean_object* v_declHint_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg(v_ref_2255_, v_msg_2256_, v_declHint_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___boxed(lean_object* v_00_u03b1_2264_, lean_object* v_ref_2265_, lean_object* v_msg_2266_, lean_object* v_declHint_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18(v_00_u03b1_2264_, v_ref_2265_, v_msg_2266_, v_declHint_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v_ref_2265_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23(lean_object* v_msg_2274_, lean_object* v_declHint_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg(v_msg_2274_, v_declHint_2275_, v___y_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___boxed(lean_object* v_msg_2282_, lean_object* v_declHint_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23(v_msg_2282_, v_declHint_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23(lean_object* v_00_u03b1_2290_, lean_object* v_ref_2291_, lean_object* v_msg_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg(v_ref_2291_, v_msg_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___boxed(lean_object* v_00_u03b1_2299_, lean_object* v_ref_2300_, lean_object* v_msg_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23(v_00_u03b1_2299_, v_ref_2300_, v_msg_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v_ref_2300_);
return v_res_2307_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Deprecated(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Deprecated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ImplementedByAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_genCtorIdx = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_genCtorIdx);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* initialize_Lean_Linter_Deprecated(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Deprecated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ImplementedByAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Constructions_CtorIdx(builtin);
}
#ifdef __cplusplus
}
#endif
