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
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg___boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1(lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__18;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__19 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__19_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__20;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__21 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__21_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__22;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__23 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__23_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__24;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__25 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__25_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__26;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_244_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg___closed__0);
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg(){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg___closed__1);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg___boxed(lean_object* v___dummy_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg();
return v_res_250_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__0(void){
_start:
{
lean_object* v___x_251_; lean_object* v___f_252_; 
v___x_251_ = l_Lean_instInhabitedExpr;
v___f_252_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___boxed), 8, 1);
lean_closure_set(v___f_252_, 0, v___x_251_);
return v___f_252_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg___closed__0);
v___x_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
return v___x_254_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3(void){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg();
return v___x_257_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
return v___x_259_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__5(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1);
v___x_262_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
lean_ctor_set(v___x_262_, 2, v___x_260_);
return v___x_262_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__6(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_263_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__5, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__5_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__5);
v___x_264_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4);
v___x_265_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1);
v___x_266_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3);
v___x_267_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v___x_265_);
lean_ctor_set(v___x_267_, 2, v___x_264_);
lean_ctor_set(v___x_267_, 3, v___x_265_);
lean_ctor_set(v___x_267_, 4, v___x_265_);
lean_ctor_set(v___x_267_, 5, v___x_265_);
lean_ctor_set(v___x_267_, 6, v___x_263_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl(lean_object* v_indName_268_, lean_object* v_levelParams_269_, lean_object* v_declType_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___f_276_; lean_object* v_implName_277_; uint8_t v___x_278_; lean_object* v___x_279_; 
v___f_276_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__0, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__0_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__0);
lean_inc(v_indName_268_);
v_implName_277_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImplName(v_indName_268_);
v___x_278_ = 0;
lean_inc_ref(v_declType_270_);
v___x_279_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg(v_declType_270_, v___f_276_, v___x_278_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___y_289_; lean_object* v___y_290_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___x_321_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc(v_a_280_);
lean_dec_ref_known(v___x_279_, 1);
lean_inc_n(v_implName_277_, 2);
v___x_281_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_281_, 0, v_implName_277_);
lean_ctor_set(v___x_281_, 1, v_levelParams_269_);
lean_ctor_set(v___x_281_, 2, v_declType_270_);
v___x_282_ = lean_box(0);
v___x_283_ = 0;
v___x_284_ = lean_box(0);
v___x_285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_285_, 0, v_implName_277_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_286_, 0, v___x_281_);
lean_ctor_set(v___x_286_, 1, v_a_280_);
lean_ctor_set(v___x_286_, 2, v___x_282_);
lean_ctor_set(v___x_286_, 3, v___x_285_);
lean_ctor_set_uint8(v___x_286_, sizeof(void*)*4, v___x_283_);
v___x_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_inc_ref(v___x_287_);
v___x_321_ = l_Lean_addDecl(v___x_287_, v___x_278_, v_a_273_, v_a_274_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v___x_322_; lean_object* v_env_323_; lean_object* v_nextMacroScope_324_; lean_object* v_ngen_325_; lean_object* v_auxDeclNGen_326_; lean_object* v_traceState_327_; lean_object* v_recordedDeps_328_; lean_object* v_messages_329_; lean_object* v_infoState_330_; lean_object* v_snapshotTasks_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_427_; 
lean_dec_ref_known(v___x_321_, 1);
v___x_322_ = lean_st_ref_take(v_a_274_);
v_env_323_ = lean_ctor_get(v___x_322_, 0);
v_nextMacroScope_324_ = lean_ctor_get(v___x_322_, 1);
v_ngen_325_ = lean_ctor_get(v___x_322_, 2);
v_auxDeclNGen_326_ = lean_ctor_get(v___x_322_, 3);
v_traceState_327_ = lean_ctor_get(v___x_322_, 4);
v_recordedDeps_328_ = lean_ctor_get(v___x_322_, 6);
v_messages_329_ = lean_ctor_get(v___x_322_, 7);
v_infoState_330_ = lean_ctor_get(v___x_322_, 8);
v_snapshotTasks_331_ = lean_ctor_get(v___x_322_, 9);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_427_ == 0)
{
lean_object* v_unused_428_; 
v_unused_428_ = lean_ctor_get(v___x_322_, 5);
lean_dec(v_unused_428_);
v___x_333_ = v___x_322_;
v_isShared_334_ = v_isSharedCheck_427_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_snapshotTasks_331_);
lean_inc(v_infoState_330_);
lean_inc(v_messages_329_);
lean_inc(v_recordedDeps_328_);
lean_inc(v_traceState_327_);
lean_inc(v_auxDeclNGen_326_);
lean_inc(v_ngen_325_);
lean_inc(v_nextMacroScope_324_);
lean_inc(v_env_323_);
lean_dec(v___x_322_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_427_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
lean_inc(v_implName_277_);
v___x_335_ = l_Lean_Meta_addToCompletionBlackList(v_env_323_, v_implName_277_);
v___x_336_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 5, v___x_336_);
lean_ctor_set(v___x_333_, 0, v___x_335_);
v___x_338_ = v___x_333_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_nextMacroScope_324_);
lean_ctor_set(v_reuseFailAlloc_426_, 2, v_ngen_325_);
lean_ctor_set(v_reuseFailAlloc_426_, 3, v_auxDeclNGen_326_);
lean_ctor_set(v_reuseFailAlloc_426_, 4, v_traceState_327_);
lean_ctor_set(v_reuseFailAlloc_426_, 5, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_426_, 6, v_recordedDeps_328_);
lean_ctor_set(v_reuseFailAlloc_426_, 7, v_messages_329_);
lean_ctor_set(v_reuseFailAlloc_426_, 8, v_infoState_330_);
lean_ctor_set(v_reuseFailAlloc_426_, 9, v_snapshotTasks_331_);
v___x_338_ = v_reuseFailAlloc_426_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v_mctx_341_; lean_object* v_zetaDeltaFVarIds_342_; lean_object* v_postponed_343_; lean_object* v_diag_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_424_; 
v___x_339_ = lean_st_ref_put(v_a_274_, v___x_338_);
v___x_340_ = lean_st_ref_take(v_a_272_);
v_mctx_341_ = lean_ctor_get(v___x_340_, 0);
v_zetaDeltaFVarIds_342_ = lean_ctor_get(v___x_340_, 2);
v_postponed_343_ = lean_ctor_get(v___x_340_, 3);
v_diag_344_ = lean_ctor_get(v___x_340_, 4);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v___x_340_, 1);
lean_dec(v_unused_425_);
v___x_346_ = v___x_340_;
v_isShared_347_ = v_isSharedCheck_424_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_diag_344_);
lean_inc(v_postponed_343_);
lean_inc(v_zetaDeltaFVarIds_342_);
lean_inc(v_mctx_341_);
lean_dec(v___x_340_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_424_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v___x_350_; 
v___x_348_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__6, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__6_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__6);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v___x_348_);
v___x_350_ = v___x_346_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_mctx_341_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_423_, 2, v_zetaDeltaFVarIds_342_);
lean_ctor_set(v_reuseFailAlloc_423_, 3, v_postponed_343_);
lean_ctor_set(v_reuseFailAlloc_423_, 4, v_diag_344_);
v___x_350_ = v_reuseFailAlloc_423_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v_env_353_; lean_object* v_nextMacroScope_354_; lean_object* v_ngen_355_; lean_object* v_auxDeclNGen_356_; lean_object* v_traceState_357_; lean_object* v_recordedDeps_358_; lean_object* v_messages_359_; lean_object* v_infoState_360_; lean_object* v_snapshotTasks_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_421_; 
v___x_351_ = lean_st_ref_put(v_a_272_, v___x_350_);
v___x_352_ = lean_st_ref_take(v_a_274_);
v_env_353_ = lean_ctor_get(v___x_352_, 0);
v_nextMacroScope_354_ = lean_ctor_get(v___x_352_, 1);
v_ngen_355_ = lean_ctor_get(v___x_352_, 2);
v_auxDeclNGen_356_ = lean_ctor_get(v___x_352_, 3);
v_traceState_357_ = lean_ctor_get(v___x_352_, 4);
v_recordedDeps_358_ = lean_ctor_get(v___x_352_, 6);
v_messages_359_ = lean_ctor_get(v___x_352_, 7);
v_infoState_360_ = lean_ctor_get(v___x_352_, 8);
v_snapshotTasks_361_ = lean_ctor_get(v___x_352_, 9);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v___x_352_, 5);
lean_dec(v_unused_422_);
v___x_363_ = v___x_352_;
v_isShared_364_ = v_isSharedCheck_421_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_snapshotTasks_361_);
lean_inc(v_infoState_360_);
lean_inc(v_messages_359_);
lean_inc(v_recordedDeps_358_);
lean_inc(v_traceState_357_);
lean_inc(v_auxDeclNGen_356_);
lean_inc(v_ngen_355_);
lean_inc(v_nextMacroScope_354_);
lean_inc(v_env_353_);
lean_dec(v___x_352_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_421_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_367_; 
lean_inc(v_implName_277_);
v___x_365_ = l_Lean_addProtected(v_env_353_, v_implName_277_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 5, v___x_336_);
lean_ctor_set(v___x_363_, 0, v___x_365_);
v___x_367_ = v___x_363_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_nextMacroScope_354_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v_ngen_355_);
lean_ctor_set(v_reuseFailAlloc_420_, 3, v_auxDeclNGen_356_);
lean_ctor_set(v_reuseFailAlloc_420_, 4, v_traceState_357_);
lean_ctor_set(v_reuseFailAlloc_420_, 5, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_420_, 6, v_recordedDeps_358_);
lean_ctor_set(v_reuseFailAlloc_420_, 7, v_messages_359_);
lean_ctor_set(v_reuseFailAlloc_420_, 8, v_infoState_360_);
lean_ctor_set(v_reuseFailAlloc_420_, 9, v_snapshotTasks_361_);
v___x_367_ = v_reuseFailAlloc_420_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v_mctx_370_; lean_object* v_zetaDeltaFVarIds_371_; lean_object* v_postponed_372_; lean_object* v_diag_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_418_; 
v___x_368_ = lean_st_ref_put(v_a_274_, v___x_367_);
v___x_369_ = lean_st_ref_take(v_a_272_);
v_mctx_370_ = lean_ctor_get(v___x_369_, 0);
v_zetaDeltaFVarIds_371_ = lean_ctor_get(v___x_369_, 2);
v_postponed_372_ = lean_ctor_get(v___x_369_, 3);
v_diag_373_ = lean_ctor_get(v___x_369_, 4);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; 
v_unused_419_ = lean_ctor_get(v___x_369_, 1);
lean_dec(v_unused_419_);
v___x_375_ = v___x_369_;
v_isShared_376_ = v_isSharedCheck_418_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_diag_373_);
lean_inc(v_postponed_372_);
lean_inc(v_zetaDeltaFVarIds_371_);
lean_inc(v_mctx_370_);
lean_dec(v___x_369_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_418_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 1, v___x_348_);
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_mctx_370_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_zetaDeltaFVarIds_371_);
lean_ctor_set(v_reuseFailAlloc_417_, 3, v_postponed_372_);
lean_ctor_set(v_reuseFailAlloc_417_, 4, v_diag_373_);
v___x_378_ = v_reuseFailAlloc_417_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v_env_381_; uint8_t v___x_382_; 
v___x_379_ = lean_st_ref_put(v_a_272_, v___x_378_);
v___x_380_ = lean_st_ref_get(v_a_274_);
v_env_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc_ref(v_env_381_);
lean_dec(v___x_380_);
v___x_382_ = l_Lean_isMarkedMeta(v_env_381_, v_indName_268_);
if (v___x_382_ == 0)
{
v___y_289_ = v_a_271_;
v___y_290_ = v_a_272_;
v___y_291_ = v_a_273_;
v___y_292_ = v_a_274_;
goto v___jp_288_;
}
else
{
lean_object* v___x_383_; lean_object* v_env_384_; lean_object* v_nextMacroScope_385_; lean_object* v_ngen_386_; lean_object* v_auxDeclNGen_387_; lean_object* v_traceState_388_; lean_object* v_recordedDeps_389_; lean_object* v_messages_390_; lean_object* v_infoState_391_; lean_object* v_snapshotTasks_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_415_; 
v___x_383_ = lean_st_ref_take(v_a_274_);
v_env_384_ = lean_ctor_get(v___x_383_, 0);
v_nextMacroScope_385_ = lean_ctor_get(v___x_383_, 1);
v_ngen_386_ = lean_ctor_get(v___x_383_, 2);
v_auxDeclNGen_387_ = lean_ctor_get(v___x_383_, 3);
v_traceState_388_ = lean_ctor_get(v___x_383_, 4);
v_recordedDeps_389_ = lean_ctor_get(v___x_383_, 6);
v_messages_390_ = lean_ctor_get(v___x_383_, 7);
v_infoState_391_ = lean_ctor_get(v___x_383_, 8);
v_snapshotTasks_392_ = lean_ctor_get(v___x_383_, 9);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; 
v_unused_416_ = lean_ctor_get(v___x_383_, 5);
lean_dec(v_unused_416_);
v___x_394_ = v___x_383_;
v_isShared_395_ = v_isSharedCheck_415_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_snapshotTasks_392_);
lean_inc(v_infoState_391_);
lean_inc(v_messages_390_);
lean_inc(v_recordedDeps_389_);
lean_inc(v_traceState_388_);
lean_inc(v_auxDeclNGen_387_);
lean_inc(v_ngen_386_);
lean_inc(v_nextMacroScope_385_);
lean_inc(v_env_384_);
lean_dec(v___x_383_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_415_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_398_; 
lean_inc(v_implName_277_);
v___x_396_ = l_Lean_markMeta(v_env_384_, v_implName_277_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 5, v___x_336_);
lean_ctor_set(v___x_394_, 0, v___x_396_);
v___x_398_ = v___x_394_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_396_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_nextMacroScope_385_);
lean_ctor_set(v_reuseFailAlloc_414_, 2, v_ngen_386_);
lean_ctor_set(v_reuseFailAlloc_414_, 3, v_auxDeclNGen_387_);
lean_ctor_set(v_reuseFailAlloc_414_, 4, v_traceState_388_);
lean_ctor_set(v_reuseFailAlloc_414_, 5, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_414_, 6, v_recordedDeps_389_);
lean_ctor_set(v_reuseFailAlloc_414_, 7, v_messages_390_);
lean_ctor_set(v_reuseFailAlloc_414_, 8, v_infoState_391_);
lean_ctor_set(v_reuseFailAlloc_414_, 9, v_snapshotTasks_392_);
v___x_398_ = v_reuseFailAlloc_414_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_mctx_401_; lean_object* v_zetaDeltaFVarIds_402_; lean_object* v_postponed_403_; lean_object* v_diag_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_412_; 
v___x_399_ = lean_st_ref_put(v_a_274_, v___x_398_);
v___x_400_ = lean_st_ref_take(v_a_272_);
v_mctx_401_ = lean_ctor_get(v___x_400_, 0);
v_zetaDeltaFVarIds_402_ = lean_ctor_get(v___x_400_, 2);
v_postponed_403_ = lean_ctor_get(v___x_400_, 3);
v_diag_404_ = lean_ctor_get(v___x_400_, 4);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; 
v_unused_413_ = lean_ctor_get(v___x_400_, 1);
lean_dec(v_unused_413_);
v___x_406_ = v___x_400_;
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_diag_404_);
lean_inc(v_postponed_403_);
lean_inc(v_zetaDeltaFVarIds_402_);
lean_inc(v_mctx_401_);
lean_dec(v___x_400_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_412_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 1, v___x_348_);
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_mctx_401_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_zetaDeltaFVarIds_402_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_postponed_403_);
lean_ctor_set(v_reuseFailAlloc_411_, 4, v_diag_404_);
v___x_409_ = v_reuseFailAlloc_411_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_410_; 
v___x_410_ = lean_st_ref_put(v_a_272_, v___x_409_);
v___y_289_ = v_a_271_;
v___y_290_ = v_a_272_;
v___y_291_ = v_a_273_;
v___y_292_ = v_a_274_;
goto v___jp_288_;
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
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec_ref_known(v___x_287_, 1);
lean_dec(v_implName_277_);
lean_dec(v_indName_268_);
v_a_429_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_321_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_321_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
v___jp_288_:
{
uint8_t v___x_293_; lean_object* v___x_294_; 
v___x_293_ = 4;
lean_inc(v_implName_277_);
v___x_294_ = l_Lean_Meta_setInlineAttribute(v_implName_277_, v___x_293_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
if (lean_obj_tag(v___x_294_) == 0)
{
uint8_t v___x_295_; lean_object* v___x_296_; 
lean_dec_ref_known(v___x_294_, 1);
v___x_295_ = 1;
v___x_296_ = l_Lean_compileDecl(v___x_287_, v___x_295_, v___y_291_, v___y_292_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_303_ == 0)
{
lean_object* v_unused_304_; 
v_unused_304_ = lean_ctor_get(v___x_296_, 0);
lean_dec(v_unused_304_);
v___x_298_ = v___x_296_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_dec(v___x_296_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v_implName_277_);
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_implName_277_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_dec(v_implName_277_);
v_a_305_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_296_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_296_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_dec_ref_known(v___x_287_, 1);
lean_dec(v_implName_277_);
v_a_313_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_294_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_294_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
lean_dec(v_implName_277_);
lean_dec_ref(v_declType_270_);
lean_dec(v_levelParams_269_);
lean_dec(v_indName_268_);
v_a_437_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_279_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_279_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___boxed(lean_object* v_indName_445_, lean_object* v_levelParams_446_, lean_object* v_declType_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl(v_indName_445_, v_levelParams_446_, v_declType_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1(lean_object* v_00_u03b2_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1___redArg(){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1___redArg___boxed(lean_object* v___dummy_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1___redArg();
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1(lean_object* v_00_u03b2_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3);
return v___x_461_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(lean_object* v_opts_462_, lean_object* v_opt_463_){
_start:
{
lean_object* v_name_464_; lean_object* v_defValue_465_; lean_object* v_map_466_; lean_object* v___x_467_; 
v_name_464_ = lean_ctor_get(v_opt_463_, 0);
v_defValue_465_ = lean_ctor_get(v_opt_463_, 1);
v_map_466_ = lean_ctor_get(v_opts_462_, 0);
v___x_467_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_466_, v_name_464_);
if (lean_obj_tag(v___x_467_) == 0)
{
uint8_t v___x_468_; 
v___x_468_ = lean_unbox(v_defValue_465_);
return v___x_468_;
}
else
{
lean_object* v_val_469_; 
v_val_469_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_val_469_);
lean_dec_ref_known(v___x_467_, 1);
if (lean_obj_tag(v_val_469_) == 1)
{
uint8_t v_v_470_; 
v_v_470_ = lean_ctor_get_uint8(v_val_469_, 0);
lean_dec_ref_known(v_val_469_, 0);
return v_v_470_;
}
else
{
uint8_t v___x_471_; 
lean_dec(v_val_469_);
v___x_471_ = lean_unbox(v_defValue_465_);
return v___x_471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0___boxed(lean_object* v_opts_472_, lean_object* v_opt_473_){
_start:
{
uint8_t v_res_474_; lean_object* v_r_475_; 
v_res_474_ = l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(v_opts_472_, v_opt_473_);
lean_dec_ref(v_opt_473_);
lean_dec_ref(v_opts_472_);
v_r_475_ = lean_box(v_res_474_);
return v_r_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(lean_object* v_constName_476_, uint8_t v_skipRealize_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; lean_object* v_env_481_; uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_480_ = lean_st_ref_get(v___y_478_);
v_env_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc_ref(v_env_481_);
lean_dec(v___x_480_);
v___x_482_ = l_Lean_Environment_contains(v_env_481_, v_constName_476_, v_skipRealize_477_);
v___x_483_ = lean_box(v___x_482_);
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg___boxed(lean_object* v_constName_485_, lean_object* v_skipRealize_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
uint8_t v_skipRealize_boxed_489_; lean_object* v_res_490_; 
v_skipRealize_boxed_489_ = lean_unbox(v_skipRealize_486_);
v_res_490_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v_constName_485_, v_skipRealize_boxed_489_, v___y_487_);
lean_dec(v___y_487_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1(lean_object* v_constName_491_, uint8_t v_skipRealize_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v_constName_491_, v_skipRealize_492_, v___y_496_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___boxed(lean_object* v_constName_499_, lean_object* v_skipRealize_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
uint8_t v_skipRealize_boxed_506_; lean_object* v_res_507_; 
v_skipRealize_boxed_506_ = lean_unbox(v_skipRealize_500_);
v_res_507_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1(v_constName_499_, v_skipRealize_boxed_506_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(lean_object* v_type_508_, lean_object* v_maxFVars_x3f_509_, lean_object* v_k_510_, uint8_t v_cleanupAnnotations_511_, uint8_t v_whnfType_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v___f_518_; lean_object* v___x_519_; 
v___f_518_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_518_, 0, v_k_510_);
v___x_519_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_508_, v_maxFVars_x3f_509_, v___f_518_, v_cleanupAnnotations_511_, v_whnfType_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_519_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
v_a_528_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_519_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_519_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___boxed(lean_object* v_type_536_, lean_object* v_maxFVars_x3f_537_, lean_object* v_k_538_, lean_object* v_cleanupAnnotations_539_, lean_object* v_whnfType_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_546_; uint8_t v_whnfType_boxed_547_; lean_object* v_res_548_; 
v_cleanupAnnotations_boxed_546_ = lean_unbox(v_cleanupAnnotations_539_);
v_whnfType_boxed_547_ = lean_unbox(v_whnfType_540_);
v_res_548_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_536_, v_maxFVars_x3f_537_, v_k_538_, v_cleanupAnnotations_boxed_546_, v_whnfType_boxed_547_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5(lean_object* v_00_u03b1_549_, lean_object* v_type_550_, lean_object* v_maxFVars_x3f_551_, lean_object* v_k_552_, uint8_t v_cleanupAnnotations_553_, uint8_t v_whnfType_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_550_, v_maxFVars_x3f_551_, v_k_552_, v_cleanupAnnotations_553_, v_whnfType_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___boxed(lean_object* v_00_u03b1_561_, lean_object* v_type_562_, lean_object* v_maxFVars_x3f_563_, lean_object* v_k_564_, lean_object* v_cleanupAnnotations_565_, lean_object* v_whnfType_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_572_; uint8_t v_whnfType_boxed_573_; lean_object* v_res_574_; 
v_cleanupAnnotations_boxed_572_ = lean_unbox(v_cleanupAnnotations_565_);
v_whnfType_boxed_573_ = lean_unbox(v_whnfType_566_);
v_res_574_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5(v_00_u03b1_561_, v_type_562_, v_maxFVars_x3f_563_, v_k_564_, v_cleanupAnnotations_boxed_572_, v_whnfType_boxed_573_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(lean_object* v_name_575_, lean_object* v_levelParams_576_, lean_object* v_type_577_, lean_object* v_value_578_, lean_object* v_hints_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_582_; uint8_t v___y_584_; lean_object* v_env_592_; uint8_t v___x_593_; 
v___x_582_ = lean_st_ref_get(v___y_580_);
v_env_592_ = lean_ctor_get(v___x_582_, 0);
lean_inc_ref_n(v_env_592_, 2);
lean_dec(v___x_582_);
v___x_593_ = l_Lean_Environment_hasUnsafe(v_env_592_, v_type_577_);
if (v___x_593_ == 0)
{
uint8_t v___x_594_; 
v___x_594_ = l_Lean_Environment_hasUnsafe(v_env_592_, v_value_578_);
if (v___x_594_ == 0)
{
uint8_t v___x_595_; 
v___x_595_ = 1;
v___y_584_ = v___x_595_;
goto v___jp_583_;
}
else
{
goto v___jp_590_;
}
}
else
{
lean_dec_ref(v_env_592_);
goto v___jp_590_;
}
v___jp_583_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
lean_inc(v_name_575_);
v___x_585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_585_, 0, v_name_575_);
lean_ctor_set(v___x_585_, 1, v_levelParams_576_);
lean_ctor_set(v___x_585_, 2, v_type_577_);
v___x_586_ = lean_box(0);
v___x_587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_587_, 0, v_name_575_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_588_, 0, v___x_585_);
lean_ctor_set(v___x_588_, 1, v_value_578_);
lean_ctor_set(v___x_588_, 2, v_hints_579_);
lean_ctor_set(v___x_588_, 3, v___x_587_);
lean_ctor_set_uint8(v___x_588_, sizeof(void*)*4, v___y_584_);
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
return v___x_589_;
}
v___jp_590_:
{
uint8_t v___x_591_; 
v___x_591_ = 0;
v___y_584_ = v___x_591_;
goto v___jp_583_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg___boxed(lean_object* v_name_596_, lean_object* v_levelParams_597_, lean_object* v_type_598_, lean_object* v_value_599_, lean_object* v_hints_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v_name_596_, v_levelParams_597_, v_type_598_, v_value_599_, v_hints_600_, v___y_601_);
lean_dec(v___y_601_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8(lean_object* v_name_604_, lean_object* v_levelParams_605_, lean_object* v_type_606_, lean_object* v_value_607_, lean_object* v_hints_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v_name_604_, v_levelParams_605_, v_type_606_, v_value_607_, v_hints_608_, v___y_612_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___boxed(lean_object* v_name_615_, lean_object* v_levelParams_616_, lean_object* v_type_617_, lean_object* v_value_618_, lean_object* v_hints_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8(v_name_615_, v_levelParams_616_, v_type_617_, v_value_618_, v_hints_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCtorIdx_spec__11(lean_object* v_msg_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___f_633_; lean_object* v___x_13918__overap_634_; lean_object* v___x_635_; 
v___f_633_ = ((lean_object*)(l_panic___at___00Lean_mkCtorIdx_spec__11___closed__0));
v___x_13918__overap_634_ = lean_panic_fn_borrowed(v___f_633_, v_msg_627_);
lean_inc(v___y_631_);
lean_inc_ref(v___y_630_);
lean_inc(v___y_629_);
lean_inc_ref(v___y_628_);
v___x_635_ = lean_apply_5(v___x_13918__overap_634_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, lean_box(0));
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCtorIdx_spec__11___boxed(lean_object* v_msg_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_panic___at___00Lean_mkCtorIdx_spec__11(v_msg_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(lean_object* v_cidx_643_, uint8_t v___x_644_, uint8_t v___x_645_, uint8_t v___x_646_, lean_object* v_ys_647_, lean_object* v_x_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = l_Lean_mkRawNatLit(v_cidx_643_);
v___x_655_ = l_Lean_Meta_mkLambdaFVars(v_ys_647_, v___x_654_, v___x_644_, v___x_645_, v___x_644_, v___x_645_, v___x_646_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed(lean_object* v_cidx_656_, lean_object* v___x_657_, lean_object* v___x_658_, lean_object* v___x_659_, lean_object* v_ys_660_, lean_object* v_x_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
uint8_t v___x_21412__boxed_667_; uint8_t v___x_21413__boxed_668_; uint8_t v___x_21414__boxed_669_; lean_object* v_res_670_; 
v___x_21412__boxed_667_ = lean_unbox(v___x_657_);
v___x_21413__boxed_668_ = lean_unbox(v___x_658_);
v___x_21414__boxed_669_ = lean_unbox(v___x_659_);
v_res_670_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(v_cidx_656_, v___x_21412__boxed_667_, v___x_21413__boxed_668_, v___x_21414__boxed_669_, v_ys_660_, v_x_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec_ref(v_x_661_);
lean_dec_ref(v_ys_660_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__10(lean_object* v_msgData_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v___x_677_; lean_object* v_env_678_; uint8_t v___x_679_; lean_object* v_env_680_; lean_object* v___x_681_; lean_object* v_toCold_682_; lean_object* v_mctx_683_; lean_object* v_lctx_684_; lean_object* v_options_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_677_ = lean_st_ref_get(v___y_675_);
v_env_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc_ref(v_env_678_);
lean_dec(v___x_677_);
v___x_679_ = 0;
v_env_680_ = l_Lean_Environment_setRecordingDeps(v_env_678_, v___x_679_);
v___x_681_ = lean_st_ref_get(v___y_673_);
v_toCold_682_ = lean_ctor_get(v___y_674_, 0);
v_mctx_683_ = lean_ctor_get(v___x_681_, 0);
lean_inc_ref(v_mctx_683_);
lean_dec(v___x_681_);
v_lctx_684_ = lean_ctor_get(v___y_672_, 2);
v_options_685_ = lean_ctor_get(v_toCold_682_, 2);
lean_inc_ref(v_options_685_);
lean_inc_ref(v_lctx_684_);
v___x_686_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_686_, 0, v_env_680_);
lean_ctor_set(v___x_686_, 1, v_mctx_683_);
lean_ctor_set(v___x_686_, 2, v_lctx_684_);
lean_ctor_set(v___x_686_, 3, v_options_685_);
v___x_687_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v_msgData_671_);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__10___boxed(lean_object* v_msgData_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__10(v_msgData_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(lean_object* v_msg_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_ref_702_; lean_object* v___x_703_; lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_712_; 
v_ref_702_ = lean_ctor_get(v___y_699_, 2);
v___x_703_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__10(v_msg_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
v_a_704_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_712_ == 0)
{
v___x_706_ = v___x_703_;
v_isShared_707_ = v_isSharedCheck_712_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_703_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_712_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; lean_object* v___x_710_; 
lean_inc(v_ref_702_);
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v_ref_702_);
lean_ctor_set(v___x_708_, 1, v_a_704_);
if (v_isShared_707_ == 0)
{
lean_ctor_set_tag(v___x_706_, 1);
lean_ctor_set(v___x_706_, 0, v___x_708_);
v___x_710_ = v___x_706_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg___boxed(lean_object* v_msg_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
return v_res_719_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0(void){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_instMonadEIO___redArg();
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(lean_object* v_msg_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v_toApplicative_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_794_; 
v___x_731_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0);
v___x_732_ = l_StateRefT_x27_instMonad___redArg(v___x_731_);
v_toApplicative_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; 
v_unused_795_ = lean_ctor_get(v___x_732_, 1);
lean_dec(v_unused_795_);
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_794_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_toApplicative_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_794_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v_toFunctor_737_; lean_object* v_toSeq_738_; lean_object* v_toSeqLeft_739_; lean_object* v_toSeqRight_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_792_; 
v_toFunctor_737_ = lean_ctor_get(v_toApplicative_733_, 0);
v_toSeq_738_ = lean_ctor_get(v_toApplicative_733_, 2);
v_toSeqLeft_739_ = lean_ctor_get(v_toApplicative_733_, 3);
v_toSeqRight_740_ = lean_ctor_get(v_toApplicative_733_, 4);
v_isSharedCheck_792_ = !lean_is_exclusive(v_toApplicative_733_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v_toApplicative_733_, 1);
lean_dec(v_unused_793_);
v___x_742_ = v_toApplicative_733_;
v_isShared_743_ = v_isSharedCheck_792_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_toSeqRight_740_);
lean_inc(v_toSeqLeft_739_);
lean_inc(v_toSeq_738_);
lean_inc(v_toFunctor_737_);
lean_dec(v_toApplicative_733_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_792_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___f_744_; lean_object* v___f_745_; lean_object* v___f_746_; lean_object* v___f_747_; lean_object* v___x_748_; lean_object* v___f_749_; lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___x_753_; 
v___f_744_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__1));
v___f_745_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__2));
lean_inc_ref(v_toFunctor_737_);
v___f_746_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_746_, 0, v_toFunctor_737_);
v___f_747_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_747_, 0, v_toFunctor_737_);
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v___f_746_);
lean_ctor_set(v___x_748_, 1, v___f_747_);
v___f_749_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_749_, 0, v_toSeqRight_740_);
v___f_750_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_750_, 0, v_toSeqLeft_739_);
v___f_751_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_751_, 0, v_toSeq_738_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 4, v___f_749_);
lean_ctor_set(v___x_742_, 3, v___f_750_);
lean_ctor_set(v___x_742_, 2, v___f_751_);
lean_ctor_set(v___x_742_, 1, v___f_744_);
lean_ctor_set(v___x_742_, 0, v___x_748_);
v___x_753_ = v___x_742_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v___f_744_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v___f_751_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v___f_750_);
lean_ctor_set(v_reuseFailAlloc_791_, 4, v___f_749_);
v___x_753_ = v_reuseFailAlloc_791_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_755_; 
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v___f_745_);
lean_ctor_set(v___x_735_, 0, v___x_753_);
v___x_755_ = v___x_735_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___f_745_);
v___x_755_ = v_reuseFailAlloc_790_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_756_; lean_object* v_toApplicative_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_788_; 
v___x_756_ = l_StateRefT_x27_instMonad___redArg(v___x_755_);
v_toApplicative_757_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v___x_756_, 1);
lean_dec(v_unused_789_);
v___x_759_ = v___x_756_;
v_isShared_760_ = v_isSharedCheck_788_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_toApplicative_757_);
lean_dec(v___x_756_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_788_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v_toFunctor_761_; lean_object* v_toSeq_762_; lean_object* v_toSeqLeft_763_; lean_object* v_toSeqRight_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_786_; 
v_toFunctor_761_ = lean_ctor_get(v_toApplicative_757_, 0);
v_toSeq_762_ = lean_ctor_get(v_toApplicative_757_, 2);
v_toSeqLeft_763_ = lean_ctor_get(v_toApplicative_757_, 3);
v_toSeqRight_764_ = lean_ctor_get(v_toApplicative_757_, 4);
v_isSharedCheck_786_ = !lean_is_exclusive(v_toApplicative_757_);
if (v_isSharedCheck_786_ == 0)
{
lean_object* v_unused_787_; 
v_unused_787_ = lean_ctor_get(v_toApplicative_757_, 1);
lean_dec(v_unused_787_);
v___x_766_ = v_toApplicative_757_;
v_isShared_767_ = v_isSharedCheck_786_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_toSeqRight_764_);
lean_inc(v_toSeqLeft_763_);
lean_inc(v_toSeq_762_);
lean_inc(v_toFunctor_761_);
lean_dec(v_toApplicative_757_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_786_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___f_768_; lean_object* v___f_769_; lean_object* v___f_770_; lean_object* v___f_771_; lean_object* v___x_772_; lean_object* v___f_773_; lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___x_777_; 
v___f_768_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__3));
v___f_769_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__4));
lean_inc_ref(v_toFunctor_761_);
v___f_770_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_770_, 0, v_toFunctor_761_);
v___f_771_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_771_, 0, v_toFunctor_761_);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v___f_770_);
lean_ctor_set(v___x_772_, 1, v___f_771_);
v___f_773_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_773_, 0, v_toSeqRight_764_);
v___f_774_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_774_, 0, v_toSeqLeft_763_);
v___f_775_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_775_, 0, v_toSeq_762_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 4, v___f_773_);
lean_ctor_set(v___x_766_, 3, v___f_774_);
lean_ctor_set(v___x_766_, 2, v___f_775_);
lean_ctor_set(v___x_766_, 1, v___f_768_);
lean_ctor_set(v___x_766_, 0, v___x_772_);
v___x_777_ = v___x_766_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v___f_768_);
lean_ctor_set(v_reuseFailAlloc_785_, 2, v___f_775_);
lean_ctor_set(v_reuseFailAlloc_785_, 3, v___f_774_);
lean_ctor_set(v_reuseFailAlloc_785_, 4, v___f_773_);
v___x_777_ = v_reuseFailAlloc_785_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_779_; 
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 1, v___f_769_);
lean_ctor_set(v___x_759_, 0, v___x_777_);
v___x_779_ = v___x_759_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v___f_769_);
v___x_779_ = v_reuseFailAlloc_784_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_17649__overap_782_; lean_object* v___x_783_; 
v___x_780_ = lean_box(0);
v___x_781_ = l_instInhabitedOfMonad___redArg(v___x_779_, v___x_780_);
v___x_17649__overap_782_ = lean_panic_fn_borrowed(v___x_781_, v_msg_725_);
lean_dec(v___x_781_);
lean_inc(v___y_729_);
lean_inc_ref(v___y_728_);
lean_inc(v___y_727_);
lean_inc_ref(v___y_726_);
v___x_783_ = lean_apply_5(v___x_17649__overap_782_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, lean_box(0));
return v___x_783_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___boxed(lean_object* v_msg_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(v_msg_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
return v_res_802_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__0));
v___x_805_ = l_Lean_stringToMessageData(v___x_804_);
return v___x_805_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__2));
v___x_808_ = l_Lean_stringToMessageData(v___x_807_);
return v___x_808_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_812_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6));
v___x_813_ = lean_unsigned_to_nat(11u);
v___x_814_ = lean_unsigned_to_nat(122u);
v___x_815_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__5));
v___x_816_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__4));
v___x_817_ = l_mkPanicMessageWithDecl(v___x_816_, v___x_815_, v___x_814_, v___x_813_, v___x_812_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(lean_object* v_constName_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v___x_832_; lean_object* v_env_833_; uint8_t v___x_834_; lean_object* v___x_835_; 
v___x_832_ = lean_st_ref_get(v___y_822_);
v_env_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc_ref(v_env_833_);
lean_dec(v___x_832_);
v___x_834_ = 0;
lean_inc(v_constName_818_);
v___x_835_ = l_Lean_Environment_findAsync_x3f(v_env_833_, v_constName_818_, v___x_834_);
if (lean_obj_tag(v___x_835_) == 1)
{
lean_object* v_val_836_; uint8_t v_kind_837_; 
v_val_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_val_836_);
lean_dec_ref_known(v___x_835_, 1);
v_kind_837_ = lean_ctor_get_uint8(v_val_836_, sizeof(void*)*3);
if (v_kind_837_ == 6)
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_836_);
if (lean_obj_tag(v___x_838_) == 6)
{
lean_object* v_val_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec(v_constName_818_);
v_val_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_val_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
lean_ctor_set_tag(v___x_841_, 0);
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_val_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
else
{
lean_object* v___x_847_; lean_object* v___x_848_; 
lean_dec_ref(v___x_838_);
v___x_847_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7);
v___x_848_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(v___x_847_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_857_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_857_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_857_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_857_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
if (lean_obj_tag(v_a_849_) == 0)
{
lean_del_object(v___x_851_);
goto v___jp_824_;
}
else
{
lean_object* v_val_853_; lean_object* v___x_855_; 
lean_dec(v_constName_818_);
v_val_853_ = lean_ctor_get(v_a_849_, 0);
lean_inc(v_val_853_);
lean_dec_ref_known(v_a_849_, 1);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v_val_853_);
v___x_855_ = v___x_851_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_val_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec(v_constName_818_);
v_a_858_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_848_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_848_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
else
{
lean_dec(v_val_836_);
goto v___jp_824_;
}
}
else
{
lean_dec(v___x_835_);
goto v___jp_824_;
}
v___jp_824_:
{
lean_object* v___x_825_; uint8_t v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_825_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1);
v___x_826_ = 0;
v___x_827_ = l_Lean_MessageData_ofConstName(v_constName_818_, v___x_826_);
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_825_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3);
v___x_830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_828_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v___x_830_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___boxed(lean_object* v_constName_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(v_constName_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(uint8_t v___x_873_, lean_object* v___x_874_, lean_object* v_as_x27_875_, lean_object* v_b_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
if (lean_obj_tag(v_as_x27_875_) == 0)
{
lean_object* v___x_882_; 
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v_b_876_);
return v___x_882_;
}
else
{
lean_object* v_head_883_; lean_object* v_tail_884_; uint8_t v___x_885_; uint8_t v___x_886_; lean_object* v___x_887_; 
v_head_883_ = lean_ctor_get(v_as_x27_875_, 0);
v_tail_884_ = lean_ctor_get(v_as_x27_875_, 1);
v___x_885_ = 0;
v___x_886_ = 1;
lean_inc(v_head_883_);
v___x_887_ = l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(v_head_883_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v_toConstantVal_889_; lean_object* v_cidx_890_; lean_object* v_numFields_891_; lean_object* v_type_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___f_896_; lean_object* v___x_897_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref_known(v___x_887_, 1);
v_toConstantVal_889_ = lean_ctor_get(v_a_888_, 0);
lean_inc_ref(v_toConstantVal_889_);
v_cidx_890_ = lean_ctor_get(v_a_888_, 2);
lean_inc(v_cidx_890_);
v_numFields_891_ = lean_ctor_get(v_a_888_, 4);
lean_inc(v_numFields_891_);
lean_dec(v_a_888_);
v_type_892_ = lean_ctor_get(v_toConstantVal_889_, 2);
lean_inc_ref(v_type_892_);
lean_dec_ref(v_toConstantVal_889_);
v___x_893_ = lean_box(v___x_885_);
v___x_894_ = lean_box(v___x_873_);
v___x_895_ = lean_box(v___x_886_);
v___f_896_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_896_, 0, v_cidx_890_);
lean_closure_set(v___f_896_, 1, v___x_893_);
lean_closure_set(v___f_896_, 2, v___x_894_);
lean_closure_set(v___f_896_, 3, v___x_895_);
v___x_897_ = l_Lean_Meta_instantiateForall(v_type_892_, v___x_874_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_909_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_909_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_909_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_909_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set_tag(v___x_900_, 1);
lean_ctor_set(v___x_900_, 0, v_numFields_891_);
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_numFields_891_);
v___x_903_ = v_reuseFailAlloc_908_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_a_898_, v___x_903_, v___f_896_, v___x_885_, v___x_885_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_906_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v___x_904_, 1);
v___x_906_ = l_Lean_Expr_app___override(v_b_876_, v_a_905_);
v_as_x27_875_ = v_tail_884_;
v_b_876_ = v___x_906_;
goto _start;
}
else
{
lean_dec_ref(v_b_876_);
return v___x_904_;
}
}
}
}
else
{
lean_dec_ref(v___f_896_);
lean_dec(v_numFields_891_);
lean_dec_ref(v_b_876_);
return v___x_897_;
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec_ref(v_b_876_);
v_a_910_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_887_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_887_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___boxed(lean_object* v___x_918_, lean_object* v___x_919_, lean_object* v_as_x27_920_, lean_object* v_b_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
uint8_t v___x_21786__boxed_927_; lean_object* v_res_928_; 
v___x_21786__boxed_927_ = lean_unbox(v___x_918_);
v_res_928_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_21786__boxed_927_, v___x_919_, v_as_x27_920_, v_b_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v_as_x27_920_);
lean_dec_ref(v___x_919_);
return v_res_928_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___lam__0___closed__0(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = lean_box(0);
v___x_930_ = l_Lean_Level_succ___override(v___x_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0(lean_object* v_xs_931_, uint8_t v___x_932_, uint8_t v___x_933_, uint8_t v___x_934_, lean_object* v_val_935_, lean_object* v___x_936_, lean_object* v___x_937_, lean_object* v___x_938_, lean_object* v___x_939_, lean_object* v___x_940_, lean_object* v_ctors_941_, lean_object* v___x_942_, lean_object* v_x_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_value_950_; lean_object* v___x_953_; lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_953_ = l_Lean_InductiveVal_numCtors(v_val_935_);
v___x_954_ = lean_unsigned_to_nat(1u);
v___x_955_ = lean_nat_dec_eq(v___x_953_, v___x_954_);
lean_dec(v___x_953_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; 
lean_dec(v___x_942_);
lean_inc_ref(v_x_943_);
lean_inc_ref(v___x_936_);
v___x_956_ = lean_array_push(v___x_936_, v_x_943_);
v___x_957_ = l_Lean_Meta_mkLambdaFVars(v___x_956_, v___x_937_, v___x_932_, v___x_933_, v___x_932_, v___x_933_, v___x_934_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec_ref(v___x_956_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref_known(v___x_957_, 1);
v___x_959_ = lean_obj_once(&l_Lean_mkCtorIdx___lam__0___closed__0, &l_Lean_mkCtorIdx___lam__0___closed__0_once, _init_l_Lean_mkCtorIdx___lam__0___closed__0);
v___x_960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
lean_ctor_set(v___x_960_, 1, v___x_938_);
v___x_961_ = l_Lean_mkConst(v___x_939_, v___x_960_);
v___x_962_ = l_Lean_mkAppN(v___x_961_, v___x_940_);
v___x_963_ = l_Lean_Expr_app___override(v___x_962_, v_a_958_);
v___x_964_ = l_Lean_mkAppN(v___x_963_, v___x_936_);
lean_dec_ref(v___x_936_);
lean_inc_ref(v_x_943_);
v___x_965_ = l_Lean_Expr_app___override(v___x_964_, v_x_943_);
v___x_966_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_933_, v___x_940_, v_ctors_941_, v___x_965_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_966_, 1);
v_value_950_ = v_a_967_;
goto v___jp_949_;
}
else
{
lean_dec_ref(v_x_943_);
lean_dec_ref(v_xs_931_);
return v___x_966_;
}
}
else
{
lean_dec_ref(v_x_943_);
lean_dec(v___x_939_);
lean_dec(v___x_938_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v_xs_931_);
return v___x_957_;
}
}
else
{
lean_object* v___x_968_; 
lean_dec(v___x_939_);
lean_dec(v___x_938_);
lean_dec_ref(v___x_937_);
lean_dec_ref(v___x_936_);
v___x_968_ = l_Lean_mkRawNatLit(v___x_942_);
v_value_950_ = v___x_968_;
goto v___jp_949_;
}
v___jp_949_:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = lean_array_push(v_xs_931_, v_x_943_);
v___x_952_ = l_Lean_Meta_mkLambdaFVars(v___x_951_, v_value_950_, v___x_932_, v___x_933_, v___x_932_, v___x_933_, v___x_934_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec_ref(v___x_951_);
return v___x_952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0___boxed(lean_object** _args){
lean_object* v_xs_969_ = _args[0];
lean_object* v___x_970_ = _args[1];
lean_object* v___x_971_ = _args[2];
lean_object* v___x_972_ = _args[3];
lean_object* v_val_973_ = _args[4];
lean_object* v___x_974_ = _args[5];
lean_object* v___x_975_ = _args[6];
lean_object* v___x_976_ = _args[7];
lean_object* v___x_977_ = _args[8];
lean_object* v___x_978_ = _args[9];
lean_object* v_ctors_979_ = _args[10];
lean_object* v___x_980_ = _args[11];
lean_object* v_x_981_ = _args[12];
lean_object* v___y_982_ = _args[13];
lean_object* v___y_983_ = _args[14];
lean_object* v___y_984_ = _args[15];
lean_object* v___y_985_ = _args[16];
lean_object* v___y_986_ = _args[17];
_start:
{
uint8_t v___x_21877__boxed_987_; uint8_t v___x_21878__boxed_988_; uint8_t v___x_21879__boxed_989_; lean_object* v_res_990_; 
v___x_21877__boxed_987_ = lean_unbox(v___x_970_);
v___x_21878__boxed_988_ = lean_unbox(v___x_971_);
v___x_21879__boxed_989_ = lean_unbox(v___x_972_);
v_res_990_ = l_Lean_mkCtorIdx___lam__0(v_xs_969_, v___x_21877__boxed_987_, v___x_21878__boxed_988_, v___x_21879__boxed_989_, v_val_973_, v___x_974_, v___x_975_, v___x_976_, v___x_977_, v___x_978_, v_ctors_979_, v___x_980_, v_x_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v_ctors_979_);
lean_dec_ref(v___x_978_);
lean_dec_ref(v_val_973_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(lean_object* v_k_991_, lean_object* v_b_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; 
lean_inc(v___y_996_);
lean_inc_ref(v___y_995_);
lean_inc(v___y_994_);
lean_inc_ref(v___y_993_);
v___x_998_ = lean_apply_6(v_k_991_, v_b_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, lean_box(0));
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(lean_object* v_k_999_, lean_object* v_b_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(v_k_999_, v_b_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(lean_object* v_name_1007_, uint8_t v_bi_1008_, lean_object* v_type_1009_, lean_object* v_k_1010_, uint8_t v_kind_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___f_1017_; lean_object* v___x_1018_; 
v___f_1017_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1017_, 0, v_k_1010_);
v___x_1018_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1007_, v_bi_1008_, v_type_1009_, v___f_1017_, v_kind_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
v_a_1027_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1018_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1018_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___boxed(lean_object* v_name_1035_, lean_object* v_bi_1036_, lean_object* v_type_1037_, lean_object* v_k_1038_, lean_object* v_kind_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
uint8_t v_bi_boxed_1045_; uint8_t v_kind_boxed_1046_; lean_object* v_res_1047_; 
v_bi_boxed_1045_ = lean_unbox(v_bi_1036_);
v_kind_boxed_1046_ = lean_unbox(v_kind_1039_);
v_res_1047_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_1035_, v_bi_boxed_1045_, v_type_1037_, v_k_1038_, v_kind_boxed_1046_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(lean_object* v_name_1048_, lean_object* v_type_1049_, lean_object* v_k_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
uint8_t v___x_1056_; uint8_t v___x_1057_; lean_object* v___x_1058_; 
v___x_1056_ = 0;
v___x_1057_ = 0;
v___x_1058_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_1048_, v___x_1056_, v_type_1049_, v_k_1050_, v___x_1057_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg___boxed(lean_object* v_name_1059_, lean_object* v_type_1060_, lean_object* v_k_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v_name_1059_, v_type_1060_, v_k_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(lean_object* v_env_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v___x_1072_; lean_object* v_nextMacroScope_1073_; lean_object* v_ngen_1074_; lean_object* v_auxDeclNGen_1075_; lean_object* v_traceState_1076_; lean_object* v_recordedDeps_1077_; lean_object* v_messages_1078_; lean_object* v_infoState_1079_; lean_object* v_snapshotTasks_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1106_; 
v___x_1072_ = lean_st_ref_take(v___y_1070_);
v_nextMacroScope_1073_ = lean_ctor_get(v___x_1072_, 1);
v_ngen_1074_ = lean_ctor_get(v___x_1072_, 2);
v_auxDeclNGen_1075_ = lean_ctor_get(v___x_1072_, 3);
v_traceState_1076_ = lean_ctor_get(v___x_1072_, 4);
v_recordedDeps_1077_ = lean_ctor_get(v___x_1072_, 6);
v_messages_1078_ = lean_ctor_get(v___x_1072_, 7);
v_infoState_1079_ = lean_ctor_get(v___x_1072_, 8);
v_snapshotTasks_1080_ = lean_ctor_get(v___x_1072_, 9);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1106_ == 0)
{
lean_object* v_unused_1107_; lean_object* v_unused_1108_; 
v_unused_1107_ = lean_ctor_get(v___x_1072_, 5);
lean_dec(v_unused_1107_);
v_unused_1108_ = lean_ctor_get(v___x_1072_, 0);
lean_dec(v_unused_1108_);
v___x_1082_ = v___x_1072_;
v_isShared_1083_ = v_isSharedCheck_1106_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_snapshotTasks_1080_);
lean_inc(v_infoState_1079_);
lean_inc(v_messages_1078_);
lean_inc(v_recordedDeps_1077_);
lean_inc(v_traceState_1076_);
lean_inc(v_auxDeclNGen_1075_);
lean_inc(v_ngen_1074_);
lean_inc(v_nextMacroScope_1073_);
lean_dec(v___x_1072_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1106_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1084_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 5, v___x_1084_);
lean_ctor_set(v___x_1082_, 0, v_env_1068_);
v___x_1086_ = v___x_1082_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_env_1068_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_nextMacroScope_1073_);
lean_ctor_set(v_reuseFailAlloc_1105_, 2, v_ngen_1074_);
lean_ctor_set(v_reuseFailAlloc_1105_, 3, v_auxDeclNGen_1075_);
lean_ctor_set(v_reuseFailAlloc_1105_, 4, v_traceState_1076_);
lean_ctor_set(v_reuseFailAlloc_1105_, 5, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1105_, 6, v_recordedDeps_1077_);
lean_ctor_set(v_reuseFailAlloc_1105_, 7, v_messages_1078_);
lean_ctor_set(v_reuseFailAlloc_1105_, 8, v_infoState_1079_);
lean_ctor_set(v_reuseFailAlloc_1105_, 9, v_snapshotTasks_1080_);
v___x_1086_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v_mctx_1089_; lean_object* v_zetaDeltaFVarIds_1090_; lean_object* v_postponed_1091_; lean_object* v_diag_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1103_; 
v___x_1087_ = lean_st_ref_put(v___y_1070_, v___x_1086_);
v___x_1088_ = lean_st_ref_take(v___y_1069_);
v_mctx_1089_ = lean_ctor_get(v___x_1088_, 0);
v_zetaDeltaFVarIds_1090_ = lean_ctor_get(v___x_1088_, 2);
v_postponed_1091_ = lean_ctor_get(v___x_1088_, 3);
v_diag_1092_ = lean_ctor_get(v___x_1088_, 4);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1103_ == 0)
{
lean_object* v_unused_1104_; 
v_unused_1104_ = lean_ctor_get(v___x_1088_, 1);
lean_dec(v_unused_1104_);
v___x_1094_ = v___x_1088_;
v_isShared_1095_ = v_isSharedCheck_1103_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_diag_1092_);
lean_inc(v_postponed_1091_);
lean_inc(v_zetaDeltaFVarIds_1090_);
lean_inc(v_mctx_1089_);
lean_dec(v___x_1088_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1103_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1096_ = lean_box(0);
v___x_1097_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__6, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__6_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__6);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 1, v___x_1097_);
v___x_1099_ = v___x_1094_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_mctx_1089_);
lean_ctor_set(v_reuseFailAlloc_1102_, 1, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1102_, 2, v_zetaDeltaFVarIds_1090_);
lean_ctor_set(v_reuseFailAlloc_1102_, 3, v_postponed_1091_);
lean_ctor_set(v_reuseFailAlloc_1102_, 4, v_diag_1092_);
v___x_1099_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = lean_st_ref_put(v___y_1069_, v___x_1099_);
v___x_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1096_);
return v___x_1101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg___boxed(lean_object* v_env_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(v_env_1109_, v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec(v___y_1110_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9(lean_object* v_declName_1114_, lean_object* v_impName_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1121_; lean_object* v_env_1122_; lean_object* v___x_1123_; 
v___x_1121_ = lean_st_ref_get(v___y_1119_);
v_env_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc_ref(v_env_1122_);
lean_dec(v___x_1121_);
v___x_1123_ = l_Lean_Compiler_setImplementedBy(v_env_1122_, v_declName_1114_, v_impName_1115_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1133_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1126_ = v___x_1123_;
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1123_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set_tag(v___x_1126_, 3);
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = l_Lean_MessageData_ofFormat(v___x_1129_);
v___x_1131_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v___x_1130_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
return v___x_1131_;
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1135_; 
v_a_1134_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v___x_1123_, 1);
v___x_1135_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(v_a_1134_, v___y_1117_, v___y_1119_);
return v___x_1135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9___boxed(lean_object* v_declName_1136_, lean_object* v_impName_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9(v_declName_1136_, v_impName_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1(lean_object* v___x_1147_, lean_object* v___x_1148_, lean_object* v_xs_1149_, uint8_t v___x_1150_, uint8_t v___x_1151_, lean_object* v_val_1152_, lean_object* v___x_1153_, lean_object* v___x_1154_, lean_object* v___x_1155_, lean_object* v___x_1156_, lean_object* v_ctors_1157_, lean_object* v___x_1158_, lean_object* v___x_1159_, lean_object* v_levelParams_1160_, lean_object* v_indName_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v___x_1167_; 
lean_inc_ref(v___x_1148_);
lean_inc_ref(v___x_1147_);
v___x_1167_ = l_Lean_mkArrow(v___x_1147_, v___x_1148_, v___y_1164_, v___y_1165_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; uint8_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___f_1173_; lean_object* v___x_1174_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
lean_dec_ref_known(v___x_1167_, 1);
v___x_1169_ = 1;
v___x_1170_ = lean_box(v___x_1150_);
v___x_1171_ = lean_box(v___x_1151_);
v___x_1172_ = lean_box(v___x_1169_);
lean_inc(v___x_1158_);
lean_inc_ref(v_val_1152_);
lean_inc_ref(v_xs_1149_);
v___f_1173_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1173_, 0, v_xs_1149_);
lean_closure_set(v___f_1173_, 1, v___x_1170_);
lean_closure_set(v___f_1173_, 2, v___x_1171_);
lean_closure_set(v___f_1173_, 3, v___x_1172_);
lean_closure_set(v___f_1173_, 4, v_val_1152_);
lean_closure_set(v___f_1173_, 5, v___x_1153_);
lean_closure_set(v___f_1173_, 6, v___x_1148_);
lean_closure_set(v___f_1173_, 7, v___x_1154_);
lean_closure_set(v___f_1173_, 8, v___x_1155_);
lean_closure_set(v___f_1173_, 9, v___x_1156_);
lean_closure_set(v___f_1173_, 10, v_ctors_1157_);
lean_closure_set(v___f_1173_, 11, v___x_1158_);
v___x_1174_ = l_Lean_Meta_mkForallFVars(v_xs_1149_, v_a_1168_, v___x_1150_, v___x_1151_, v___x_1151_, v___x_1169_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
lean_dec_ref(v_xs_1149_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1174_, 1);
v___x_1176_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__1___closed__1));
v___x_1177_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v___x_1176_, v___x_1147_, v___f_1173_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1179_; lean_object* v_env_1180_; uint32_t v___x_1181_; lean_object* v___x_1182_; uint32_t v___x_1183_; uint32_t v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1332_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc_n(v_a_1178_, 2);
lean_dec_ref_known(v___x_1177_, 1);
v___x_1179_ = lean_st_ref_get(v___y_1165_);
v_env_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc_ref(v_env_1180_);
lean_dec(v___x_1179_);
v___x_1181_ = l_Lean_getMaxHeight(v_env_1180_, v_a_1178_);
v___x_1182_ = lean_unsigned_to_nat(1u);
v___x_1183_ = 1;
v___x_1184_ = lean_uint32_add(v___x_1181_, v___x_1183_);
v___x_1185_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_1185_, 0, v___x_1184_);
lean_inc(v_a_1175_);
lean_inc(v_levelParams_1160_);
lean_inc(v___x_1159_);
v___x_1186_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v___x_1159_, v_levelParams_1160_, v_a_1175_, v_a_1178_, v___x_1185_, v___y_1165_);
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1189_ = v___x_1186_;
v_isShared_1190_ = v_isSharedCheck_1332_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1186_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1332_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set_tag(v___x_1189_, 1);
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___x_1219_; 
lean_inc_ref(v___x_1192_);
v___x_1219_ = l_Lean_addDecl(v___x_1192_, v___x_1150_, v___y_1164_, v___y_1165_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v___x_1220_; lean_object* v_env_1221_; lean_object* v_nextMacroScope_1222_; lean_object* v_ngen_1223_; lean_object* v_auxDeclNGen_1224_; lean_object* v_traceState_1225_; lean_object* v_recordedDeps_1226_; lean_object* v_messages_1227_; lean_object* v_infoState_1228_; lean_object* v_snapshotTasks_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1329_; 
lean_dec_ref_known(v___x_1219_, 1);
v___x_1220_ = lean_st_ref_take(v___y_1165_);
v_env_1221_ = lean_ctor_get(v___x_1220_, 0);
v_nextMacroScope_1222_ = lean_ctor_get(v___x_1220_, 1);
v_ngen_1223_ = lean_ctor_get(v___x_1220_, 2);
v_auxDeclNGen_1224_ = lean_ctor_get(v___x_1220_, 3);
v_traceState_1225_ = lean_ctor_get(v___x_1220_, 4);
v_recordedDeps_1226_ = lean_ctor_get(v___x_1220_, 6);
v_messages_1227_ = lean_ctor_get(v___x_1220_, 7);
v_infoState_1228_ = lean_ctor_get(v___x_1220_, 8);
v_snapshotTasks_1229_ = lean_ctor_get(v___x_1220_, 9);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; 
v_unused_1330_ = lean_ctor_get(v___x_1220_, 5);
lean_dec(v_unused_1330_);
v___x_1231_ = v___x_1220_;
v_isShared_1232_ = v_isSharedCheck_1329_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_snapshotTasks_1229_);
lean_inc(v_infoState_1228_);
lean_inc(v_messages_1227_);
lean_inc(v_recordedDeps_1226_);
lean_inc(v_traceState_1225_);
lean_inc(v_auxDeclNGen_1224_);
lean_inc(v_ngen_1223_);
lean_inc(v_nextMacroScope_1222_);
lean_inc(v_env_1221_);
lean_dec(v___x_1220_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1329_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
lean_inc(v___x_1159_);
v___x_1233_ = l_Lean_Meta_addToCompletionBlackList(v_env_1221_, v___x_1159_);
v___x_1234_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1);
v___x_1235_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 5, v___x_1235_);
lean_ctor_set(v___x_1231_, 0, v___x_1233_);
v___x_1237_ = v___x_1231_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_nextMacroScope_1222_);
lean_ctor_set(v_reuseFailAlloc_1328_, 2, v_ngen_1223_);
lean_ctor_set(v_reuseFailAlloc_1328_, 3, v_auxDeclNGen_1224_);
lean_ctor_set(v_reuseFailAlloc_1328_, 4, v_traceState_1225_);
lean_ctor_set(v_reuseFailAlloc_1328_, 5, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1328_, 6, v_recordedDeps_1226_);
lean_ctor_set(v_reuseFailAlloc_1328_, 7, v_messages_1227_);
lean_ctor_set(v_reuseFailAlloc_1328_, 8, v_infoState_1228_);
lean_ctor_set(v_reuseFailAlloc_1328_, 9, v_snapshotTasks_1229_);
v___x_1237_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v_mctx_1240_; lean_object* v_zetaDeltaFVarIds_1241_; lean_object* v_postponed_1242_; lean_object* v_diag_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1326_; 
v___x_1238_ = lean_st_ref_put(v___y_1165_, v___x_1237_);
v___x_1239_ = lean_st_ref_take(v___y_1163_);
v_mctx_1240_ = lean_ctor_get(v___x_1239_, 0);
v_zetaDeltaFVarIds_1241_ = lean_ctor_get(v___x_1239_, 2);
v_postponed_1242_ = lean_ctor_get(v___x_1239_, 3);
v_diag_1243_ = lean_ctor_get(v___x_1239_, 4);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1326_ == 0)
{
lean_object* v_unused_1327_; 
v_unused_1327_ = lean_ctor_get(v___x_1239_, 1);
lean_dec(v_unused_1327_);
v___x_1245_ = v___x_1239_;
v_isShared_1246_ = v_isSharedCheck_1326_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_diag_1243_);
lean_inc(v_postponed_1242_);
lean_inc(v_zetaDeltaFVarIds_1241_);
lean_inc(v_mctx_1240_);
lean_dec(v___x_1239_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1326_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1247_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3);
v___x_1248_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4);
v___x_1249_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1234_);
lean_ctor_set(v___x_1249_, 1, v___x_1234_);
lean_ctor_set(v___x_1249_, 2, v___x_1158_);
v___x_1250_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1247_);
lean_ctor_set(v___x_1250_, 1, v___x_1234_);
lean_ctor_set(v___x_1250_, 2, v___x_1248_);
lean_ctor_set(v___x_1250_, 3, v___x_1234_);
lean_ctor_set(v___x_1250_, 4, v___x_1234_);
lean_ctor_set(v___x_1250_, 5, v___x_1234_);
lean_ctor_set(v___x_1250_, 6, v___x_1249_);
lean_inc_ref(v___x_1250_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v___x_1250_);
v___x_1252_ = v___x_1245_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_mctx_1240_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1325_, 2, v_zetaDeltaFVarIds_1241_);
lean_ctor_set(v_reuseFailAlloc_1325_, 3, v_postponed_1242_);
lean_ctor_set(v_reuseFailAlloc_1325_, 4, v_diag_1243_);
v___x_1252_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v_env_1255_; lean_object* v_nextMacroScope_1256_; lean_object* v_ngen_1257_; lean_object* v_auxDeclNGen_1258_; lean_object* v_traceState_1259_; lean_object* v_recordedDeps_1260_; lean_object* v_messages_1261_; lean_object* v_infoState_1262_; lean_object* v_snapshotTasks_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1323_; 
v___x_1253_ = lean_st_ref_put(v___y_1163_, v___x_1252_);
v___x_1254_ = lean_st_ref_take(v___y_1165_);
v_env_1255_ = lean_ctor_get(v___x_1254_, 0);
v_nextMacroScope_1256_ = lean_ctor_get(v___x_1254_, 1);
v_ngen_1257_ = lean_ctor_get(v___x_1254_, 2);
v_auxDeclNGen_1258_ = lean_ctor_get(v___x_1254_, 3);
v_traceState_1259_ = lean_ctor_get(v___x_1254_, 4);
v_recordedDeps_1260_ = lean_ctor_get(v___x_1254_, 6);
v_messages_1261_ = lean_ctor_get(v___x_1254_, 7);
v_infoState_1262_ = lean_ctor_get(v___x_1254_, 8);
v_snapshotTasks_1263_ = lean_ctor_get(v___x_1254_, 9);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1323_ == 0)
{
lean_object* v_unused_1324_; 
v_unused_1324_ = lean_ctor_get(v___x_1254_, 5);
lean_dec(v_unused_1324_);
v___x_1265_ = v___x_1254_;
v_isShared_1266_ = v_isSharedCheck_1323_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_snapshotTasks_1263_);
lean_inc(v_infoState_1262_);
lean_inc(v_messages_1261_);
lean_inc(v_recordedDeps_1260_);
lean_inc(v_traceState_1259_);
lean_inc(v_auxDeclNGen_1258_);
lean_inc(v_ngen_1257_);
lean_inc(v_nextMacroScope_1256_);
lean_inc(v_env_1255_);
lean_dec(v___x_1254_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1323_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1269_; 
lean_inc(v___x_1159_);
v___x_1267_ = l_Lean_addProtected(v_env_1255_, v___x_1159_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 5, v___x_1235_);
lean_ctor_set(v___x_1265_, 0, v___x_1267_);
v___x_1269_ = v___x_1265_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1267_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_nextMacroScope_1256_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v_ngen_1257_);
lean_ctor_set(v_reuseFailAlloc_1322_, 3, v_auxDeclNGen_1258_);
lean_ctor_set(v_reuseFailAlloc_1322_, 4, v_traceState_1259_);
lean_ctor_set(v_reuseFailAlloc_1322_, 5, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1322_, 6, v_recordedDeps_1260_);
lean_ctor_set(v_reuseFailAlloc_1322_, 7, v_messages_1261_);
lean_ctor_set(v_reuseFailAlloc_1322_, 8, v_infoState_1262_);
lean_ctor_set(v_reuseFailAlloc_1322_, 9, v_snapshotTasks_1263_);
v___x_1269_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v_mctx_1272_; lean_object* v_zetaDeltaFVarIds_1273_; lean_object* v_postponed_1274_; lean_object* v_diag_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1320_; 
v___x_1270_ = lean_st_ref_put(v___y_1165_, v___x_1269_);
v___x_1271_ = lean_st_ref_take(v___y_1163_);
v_mctx_1272_ = lean_ctor_get(v___x_1271_, 0);
v_zetaDeltaFVarIds_1273_ = lean_ctor_get(v___x_1271_, 2);
v_postponed_1274_ = lean_ctor_get(v___x_1271_, 3);
v_diag_1275_ = lean_ctor_get(v___x_1271_, 4);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1320_ == 0)
{
lean_object* v_unused_1321_; 
v_unused_1321_ = lean_ctor_get(v___x_1271_, 1);
lean_dec(v_unused_1321_);
v___x_1277_ = v___x_1271_;
v_isShared_1278_ = v_isSharedCheck_1320_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_diag_1275_);
lean_inc(v_postponed_1274_);
lean_inc(v_zetaDeltaFVarIds_1273_);
lean_inc(v_mctx_1272_);
lean_dec(v___x_1271_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1320_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
lean_inc_ref(v___x_1250_);
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 1, v___x_1250_);
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_mctx_1272_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_zetaDeltaFVarIds_1273_);
lean_ctor_set(v_reuseFailAlloc_1319_, 3, v_postponed_1274_);
lean_ctor_set(v_reuseFailAlloc_1319_, 4, v_diag_1275_);
v___x_1280_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v_env_1283_; uint8_t v___x_1284_; 
v___x_1281_ = lean_st_ref_put(v___y_1163_, v___x_1280_);
v___x_1282_ = lean_st_ref_get(v___y_1165_);
v_env_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc_ref(v_env_1283_);
lean_dec(v___x_1282_);
lean_inc(v_indName_1161_);
v___x_1284_ = l_Lean_isMarkedMeta(v_env_1283_, v_indName_1161_);
if (v___x_1284_ == 0)
{
lean_dec_ref_known(v___x_1250_, 7);
v___y_1199_ = v___y_1162_;
v___y_1200_ = v___y_1163_;
v___y_1201_ = v___y_1164_;
v___y_1202_ = v___y_1165_;
goto v___jp_1198_;
}
else
{
lean_object* v___x_1285_; lean_object* v_env_1286_; lean_object* v_nextMacroScope_1287_; lean_object* v_ngen_1288_; lean_object* v_auxDeclNGen_1289_; lean_object* v_traceState_1290_; lean_object* v_recordedDeps_1291_; lean_object* v_messages_1292_; lean_object* v_infoState_1293_; lean_object* v_snapshotTasks_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1317_; 
v___x_1285_ = lean_st_ref_take(v___y_1165_);
v_env_1286_ = lean_ctor_get(v___x_1285_, 0);
v_nextMacroScope_1287_ = lean_ctor_get(v___x_1285_, 1);
v_ngen_1288_ = lean_ctor_get(v___x_1285_, 2);
v_auxDeclNGen_1289_ = lean_ctor_get(v___x_1285_, 3);
v_traceState_1290_ = lean_ctor_get(v___x_1285_, 4);
v_recordedDeps_1291_ = lean_ctor_get(v___x_1285_, 6);
v_messages_1292_ = lean_ctor_get(v___x_1285_, 7);
v_infoState_1293_ = lean_ctor_get(v___x_1285_, 8);
v_snapshotTasks_1294_ = lean_ctor_get(v___x_1285_, 9);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1317_ == 0)
{
lean_object* v_unused_1318_; 
v_unused_1318_ = lean_ctor_get(v___x_1285_, 5);
lean_dec(v_unused_1318_);
v___x_1296_ = v___x_1285_;
v_isShared_1297_ = v_isSharedCheck_1317_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_snapshotTasks_1294_);
lean_inc(v_infoState_1293_);
lean_inc(v_messages_1292_);
lean_inc(v_recordedDeps_1291_);
lean_inc(v_traceState_1290_);
lean_inc(v_auxDeclNGen_1289_);
lean_inc(v_ngen_1288_);
lean_inc(v_nextMacroScope_1287_);
lean_inc(v_env_1286_);
lean_dec(v___x_1285_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1317_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; lean_object* v___x_1300_; 
lean_inc(v___x_1159_);
v___x_1298_ = l_Lean_markMeta(v_env_1286_, v___x_1159_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 5, v___x_1235_);
lean_ctor_set(v___x_1296_, 0, v___x_1298_);
v___x_1300_ = v___x_1296_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_nextMacroScope_1287_);
lean_ctor_set(v_reuseFailAlloc_1316_, 2, v_ngen_1288_);
lean_ctor_set(v_reuseFailAlloc_1316_, 3, v_auxDeclNGen_1289_);
lean_ctor_set(v_reuseFailAlloc_1316_, 4, v_traceState_1290_);
lean_ctor_set(v_reuseFailAlloc_1316_, 5, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1316_, 6, v_recordedDeps_1291_);
lean_ctor_set(v_reuseFailAlloc_1316_, 7, v_messages_1292_);
lean_ctor_set(v_reuseFailAlloc_1316_, 8, v_infoState_1293_);
lean_ctor_set(v_reuseFailAlloc_1316_, 9, v_snapshotTasks_1294_);
v___x_1300_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v_mctx_1303_; lean_object* v_zetaDeltaFVarIds_1304_; lean_object* v_postponed_1305_; lean_object* v_diag_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1314_; 
v___x_1301_ = lean_st_ref_put(v___y_1165_, v___x_1300_);
v___x_1302_ = lean_st_ref_take(v___y_1163_);
v_mctx_1303_ = lean_ctor_get(v___x_1302_, 0);
v_zetaDeltaFVarIds_1304_ = lean_ctor_get(v___x_1302_, 2);
v_postponed_1305_ = lean_ctor_get(v___x_1302_, 3);
v_diag_1306_ = lean_ctor_get(v___x_1302_, 4);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; 
v_unused_1315_ = lean_ctor_get(v___x_1302_, 1);
lean_dec(v_unused_1315_);
v___x_1308_ = v___x_1302_;
v_isShared_1309_ = v_isSharedCheck_1314_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_diag_1306_);
lean_inc(v_postponed_1305_);
lean_inc(v_zetaDeltaFVarIds_1304_);
lean_inc(v_mctx_1303_);
lean_dec(v___x_1302_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1314_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 1, v___x_1250_);
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_mctx_1303_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v___x_1250_);
lean_ctor_set(v_reuseFailAlloc_1313_, 2, v_zetaDeltaFVarIds_1304_);
lean_ctor_set(v_reuseFailAlloc_1313_, 3, v_postponed_1305_);
lean_ctor_set(v_reuseFailAlloc_1313_, 4, v_diag_1306_);
v___x_1311_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
lean_object* v___x_1312_; 
v___x_1312_ = lean_st_ref_put(v___y_1163_, v___x_1311_);
v___y_1199_ = v___y_1162_;
v___y_1200_ = v___y_1163_;
v___y_1201_ = v___y_1164_;
v___y_1202_ = v___y_1165_;
goto v___jp_1198_;
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
lean_dec_ref(v___x_1192_);
lean_dec(v_a_1175_);
lean_dec(v_indName_1161_);
lean_dec(v_levelParams_1160_);
lean_dec(v___x_1159_);
lean_dec(v___x_1158_);
lean_dec_ref(v_val_1152_);
return v___x_1219_;
}
v___jp_1193_:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_compileDecl(v___x_1192_, v___x_1151_, v___y_1194_, v___y_1195_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v___x_1197_; 
lean_dec_ref_known(v___x_1196_, 1);
v___x_1197_ = l_Lean_enableRealizationsForConst(v___x_1159_, v___y_1194_, v___y_1195_);
return v___x_1197_;
}
else
{
lean_dec(v___x_1159_);
return v___x_1196_;
}
}
v___jp_1198_:
{
lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = l_Lean_InductiveVal_numCtors(v_val_1152_);
lean_dec_ref(v_val_1152_);
v___x_1204_ = lean_nat_dec_eq(v___x_1203_, v___x_1182_);
lean_dec(v___x_1203_);
if (v___x_1204_ == 0)
{
uint8_t v___x_1205_; 
v___x_1205_ = l_Lean_Compiler_LCNF_isRuntimeBuiltinType(v_indName_1161_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; 
v___x_1206_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl(v_indName_1161_, v_levelParams_1160_, v_a_1175_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1208_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1207_);
lean_dec_ref_known(v___x_1206_, 1);
lean_inc(v___x_1159_);
v___x_1208_ = l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9(v___x_1159_, v_a_1207_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_dec_ref_known(v___x_1208_, 1);
v___y_1194_ = v___y_1201_;
v___y_1195_ = v___y_1202_;
goto v___jp_1193_;
}
else
{
lean_dec_ref(v___x_1192_);
lean_dec(v___x_1159_);
return v___x_1208_;
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec_ref(v___x_1192_);
lean_dec(v___x_1159_);
v_a_1209_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1206_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1206_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
else
{
lean_dec(v_a_1175_);
lean_dec(v_indName_1161_);
lean_dec(v_levelParams_1160_);
v___y_1194_ = v___y_1201_;
v___y_1195_ = v___y_1202_;
goto v___jp_1193_;
}
}
else
{
uint8_t v___x_1217_; lean_object* v___x_1218_; 
lean_dec(v_a_1175_);
lean_dec(v_indName_1161_);
lean_dec(v_levelParams_1160_);
v___x_1217_ = 2;
lean_inc(v___x_1159_);
v___x_1218_ = l_Lean_Meta_setInlineAttribute(v___x_1159_, v___x_1217_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_dec_ref_known(v___x_1218_, 1);
v___y_1194_ = v___y_1201_;
v___y_1195_ = v___y_1202_;
goto v___jp_1193_;
}
else
{
lean_dec_ref(v___x_1192_);
lean_dec(v___x_1159_);
return v___x_1218_;
}
}
}
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec(v_a_1175_);
lean_dec(v_indName_1161_);
lean_dec(v_levelParams_1160_);
lean_dec(v___x_1159_);
lean_dec(v___x_1158_);
lean_dec_ref(v_val_1152_);
v_a_1333_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1177_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1177_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref(v___f_1173_);
lean_dec(v_indName_1161_);
lean_dec(v_levelParams_1160_);
lean_dec(v___x_1159_);
lean_dec(v___x_1158_);
lean_dec_ref(v_val_1152_);
lean_dec_ref(v___x_1147_);
v_a_1341_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1174_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1174_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec(v_indName_1161_);
lean_dec(v_levelParams_1160_);
lean_dec(v___x_1159_);
lean_dec(v___x_1158_);
lean_dec(v_ctors_1157_);
lean_dec_ref(v___x_1156_);
lean_dec(v___x_1155_);
lean_dec(v___x_1154_);
lean_dec_ref(v___x_1153_);
lean_dec_ref(v_val_1152_);
lean_dec_ref(v_xs_1149_);
lean_dec_ref(v___x_1148_);
lean_dec_ref(v___x_1147_);
v_a_1349_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1167_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1167_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1___boxed(lean_object** _args){
lean_object* v___x_1357_ = _args[0];
lean_object* v___x_1358_ = _args[1];
lean_object* v_xs_1359_ = _args[2];
lean_object* v___x_1360_ = _args[3];
lean_object* v___x_1361_ = _args[4];
lean_object* v_val_1362_ = _args[5];
lean_object* v___x_1363_ = _args[6];
lean_object* v___x_1364_ = _args[7];
lean_object* v___x_1365_ = _args[8];
lean_object* v___x_1366_ = _args[9];
lean_object* v_ctors_1367_ = _args[10];
lean_object* v___x_1368_ = _args[11];
lean_object* v___x_1369_ = _args[12];
lean_object* v_levelParams_1370_ = _args[13];
lean_object* v_indName_1371_ = _args[14];
lean_object* v___y_1372_ = _args[15];
lean_object* v___y_1373_ = _args[16];
lean_object* v___y_1374_ = _args[17];
lean_object* v___y_1375_ = _args[18];
lean_object* v___y_1376_ = _args[19];
_start:
{
uint8_t v___x_22201__boxed_1377_; uint8_t v___x_22202__boxed_1378_; lean_object* v_res_1379_; 
v___x_22201__boxed_1377_ = lean_unbox(v___x_1360_);
v___x_22202__boxed_1378_ = lean_unbox(v___x_1361_);
v_res_1379_ = l_Lean_mkCtorIdx___lam__1(v___x_1357_, v___x_1358_, v_xs_1359_, v___x_22201__boxed_1377_, v___x_22202__boxed_1378_, v_val_1362_, v___x_1363_, v___x_1364_, v___x_1365_, v___x_1366_, v_ctors_1367_, v___x_1368_, v___x_1369_, v_levelParams_1370_, v_indName_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15(size_t v_sz_1380_, size_t v_i_1381_, lean_object* v_bs_1382_){
_start:
{
uint8_t v___x_1383_; 
v___x_1383_ = lean_usize_dec_lt(v_i_1381_, v_sz_1380_);
if (v___x_1383_ == 0)
{
return v_bs_1382_;
}
else
{
lean_object* v_v_1384_; lean_object* v___x_1385_; lean_object* v_bs_x27_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; size_t v___x_1391_; size_t v___x_1392_; lean_object* v___x_1393_; 
v_v_1384_ = lean_array_uget(v_bs_1382_, v_i_1381_);
v___x_1385_ = lean_unsigned_to_nat(0u);
v_bs_x27_1386_ = lean_array_uset(v_bs_1382_, v_i_1381_, v___x_1385_);
v___x_1387_ = l_Lean_Expr_fvarId_x21(v_v_1384_);
lean_dec(v_v_1384_);
v___x_1388_ = 1;
v___x_1389_ = lean_box(v___x_1388_);
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1387_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
v___x_1391_ = ((size_t)1ULL);
v___x_1392_ = lean_usize_add(v_i_1381_, v___x_1391_);
v___x_1393_ = lean_array_uset(v_bs_x27_1386_, v_i_1381_, v___x_1390_);
v_i_1381_ = v___x_1392_;
v_bs_1382_ = v___x_1393_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15___boxed(lean_object* v_sz_1395_, lean_object* v_i_1396_, lean_object* v_bs_1397_){
_start:
{
size_t v_sz_boxed_1398_; size_t v_i_boxed_1399_; lean_object* v_res_1400_; 
v_sz_boxed_1398_ = lean_unbox_usize(v_sz_1395_);
lean_dec(v_sz_1395_);
v_i_boxed_1399_ = lean_unbox_usize(v_i_1396_);
lean_dec(v_i_1396_);
v_res_1400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15(v_sz_boxed_1398_, v_i_boxed_1399_, v_bs_1397_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(lean_object* v_bs_1401_, lean_object* v_k_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1401_, v_k_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1408_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
v_a_1417_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1408_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1408_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg___boxed(lean_object* v_bs_1425_, lean_object* v_k_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(v_bs_1425_, v_k_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec_ref(v_bs_1425_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(lean_object* v_bs_1433_, lean_object* v_k_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
size_t v_sz_1440_; size_t v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v_sz_1440_ = lean_array_size(v_bs_1433_);
v___x_1441_ = ((size_t)0ULL);
v___x_1442_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15(v_sz_1440_, v___x_1441_, v_bs_1433_);
v___x_1443_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(v___x_1442_, v_k_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
lean_dec_ref(v___x_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg___boxed(lean_object* v_bs_1444_, lean_object* v_k_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(v_bs_1444_, v_k_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2(lean_object* v_numParams_1455_, lean_object* v_indName_1456_, lean_object* v___x_1457_, lean_object* v___x_1458_, uint8_t v___x_1459_, uint8_t v___x_1460_, lean_object* v_val_1461_, lean_object* v___x_1462_, lean_object* v_ctors_1463_, lean_object* v___x_1464_, lean_object* v_levelParams_1465_, lean_object* v_xs_1466_, lean_object* v_x_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___f_1485_; lean_object* v___x_1486_; 
v___x_1473_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1455_);
lean_inc_ref_n(v_xs_1466_, 3);
v___x_1474_ = l_Array_toSubarray___redArg(v_xs_1466_, v___x_1473_, v_numParams_1455_);
v___x_1475_ = l_Subarray_copy___redArg(v___x_1474_);
v___x_1476_ = lean_array_get_size(v_xs_1466_);
v___x_1477_ = l_Array_toSubarray___redArg(v_xs_1466_, v_numParams_1455_, v___x_1476_);
v___x_1478_ = l_Subarray_copy___redArg(v___x_1477_);
lean_inc(v___x_1457_);
lean_inc(v_indName_1456_);
v___x_1479_ = l_Lean_mkConst(v_indName_1456_, v___x_1457_);
v___x_1480_ = l_Lean_mkAppN(v___x_1479_, v_xs_1466_);
v___x_1481_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__2___closed__1));
v___x_1482_ = l_Lean_mkConst(v___x_1481_, v___x_1458_);
v___x_1483_ = lean_box(v___x_1459_);
v___x_1484_ = lean_box(v___x_1460_);
v___f_1485_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__1___boxed), 20, 15);
lean_closure_set(v___f_1485_, 0, v___x_1480_);
lean_closure_set(v___f_1485_, 1, v___x_1482_);
lean_closure_set(v___f_1485_, 2, v_xs_1466_);
lean_closure_set(v___f_1485_, 3, v___x_1483_);
lean_closure_set(v___f_1485_, 4, v___x_1484_);
lean_closure_set(v___f_1485_, 5, v_val_1461_);
lean_closure_set(v___f_1485_, 6, v___x_1478_);
lean_closure_set(v___f_1485_, 7, v___x_1457_);
lean_closure_set(v___f_1485_, 8, v___x_1462_);
lean_closure_set(v___f_1485_, 9, v___x_1475_);
lean_closure_set(v___f_1485_, 10, v_ctors_1463_);
lean_closure_set(v___f_1485_, 11, v___x_1473_);
lean_closure_set(v___f_1485_, 12, v___x_1464_);
lean_closure_set(v___f_1485_, 13, v_levelParams_1465_);
lean_closure_set(v___f_1485_, 14, v_indName_1456_);
v___x_1486_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(v_xs_1466_, v___f_1485_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2___boxed(lean_object** _args){
lean_object* v_numParams_1487_ = _args[0];
lean_object* v_indName_1488_ = _args[1];
lean_object* v___x_1489_ = _args[2];
lean_object* v___x_1490_ = _args[3];
lean_object* v___x_1491_ = _args[4];
lean_object* v___x_1492_ = _args[5];
lean_object* v_val_1493_ = _args[6];
lean_object* v___x_1494_ = _args[7];
lean_object* v_ctors_1495_ = _args[8];
lean_object* v___x_1496_ = _args[9];
lean_object* v_levelParams_1497_ = _args[10];
lean_object* v_xs_1498_ = _args[11];
lean_object* v_x_1499_ = _args[12];
lean_object* v___y_1500_ = _args[13];
lean_object* v___y_1501_ = _args[14];
lean_object* v___y_1502_ = _args[15];
lean_object* v___y_1503_ = _args[16];
lean_object* v___y_1504_ = _args[17];
_start:
{
uint8_t v___x_22655__boxed_1505_; uint8_t v___x_22656__boxed_1506_; lean_object* v_res_1507_; 
v___x_22655__boxed_1505_ = lean_unbox(v___x_1491_);
v___x_22656__boxed_1506_ = lean_unbox(v___x_1492_);
v_res_1507_ = l_Lean_mkCtorIdx___lam__2(v_numParams_1487_, v_indName_1488_, v___x_1489_, v___x_1490_, v___x_22655__boxed_1505_, v___x_22656__boxed_1506_, v_val_1493_, v___x_1494_, v_ctors_1495_, v___x_1496_, v_levelParams_1497_, v_xs_1498_, v_x_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec_ref(v_x_1499_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(lean_object* v_a_1508_, lean_object* v_a_1509_){
_start:
{
if (lean_obj_tag(v_a_1508_) == 0)
{
lean_object* v___x_1510_; 
v___x_1510_ = l_List_reverse___redArg(v_a_1509_);
return v___x_1510_;
}
else
{
lean_object* v_head_1511_; lean_object* v_tail_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1521_; 
v_head_1511_ = lean_ctor_get(v_a_1508_, 0);
v_tail_1512_ = lean_ctor_get(v_a_1508_, 1);
v_isSharedCheck_1521_ = !lean_is_exclusive(v_a_1508_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1514_ = v_a_1508_;
v_isShared_1515_ = v_isSharedCheck_1521_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_tail_1512_);
lean_inc(v_head_1511_);
lean_dec(v_a_1508_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1521_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1516_ = l_Lean_mkLevelParam(v_head_1511_);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 1, v_a_1509_);
lean_ctor_set(v___x_1514_, 0, v___x_1516_);
v___x_1518_ = v___x_1514_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v_a_1509_);
v___x_1518_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
v_a_1508_ = v_tail_1512_;
v_a_1509_ = v___x_1518_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__1_spec__1___redArg___closed__0);
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
return v___x_1523_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__1(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1524_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__0);
v___x_1525_ = lean_unsigned_to_nat(0u);
v___x_1526_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
lean_ctor_set(v___x_1526_, 2, v___x_1525_);
lean_ctor_set(v___x_1526_, 3, v___x_1525_);
lean_ctor_set(v___x_1526_, 4, v___x_1524_);
lean_ctor_set(v___x_1526_, 5, v___x_1524_);
lean_ctor_set(v___x_1526_, 6, v___x_1524_);
lean_ctor_set(v___x_1526_, 7, v___x_1524_);
lean_ctor_set(v___x_1526_, 8, v___x_1524_);
lean_ctor_set(v___x_1526_, 9, v___x_1524_);
lean_ctor_set(v___x_1526_, 10, v___x_1524_);
return v___x_1526_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1527_ = lean_unsigned_to_nat(32u);
v___x_1528_ = lean_mk_empty_array_with_capacity(v___x_1527_);
v___x_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
return v___x_1529_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__3(void){
_start:
{
size_t v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1530_ = ((size_t)5ULL);
v___x_1531_ = lean_unsigned_to_nat(0u);
v___x_1532_ = lean_unsigned_to_nat(32u);
v___x_1533_ = lean_mk_empty_array_with_capacity(v___x_1532_);
v___x_1534_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__2);
v___x_1535_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
lean_ctor_set(v___x_1535_, 1, v___x_1533_);
lean_ctor_set(v___x_1535_, 2, v___x_1531_);
lean_ctor_set(v___x_1535_, 3, v___x_1531_);
lean_ctor_set_usize(v___x_1535_, 4, v___x_1530_);
return v___x_1535_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__4(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1536_ = lean_box(1);
v___x_1537_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__3);
v___x_1538_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__0);
v___x_1539_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
lean_ctor_set(v___x_1539_, 1, v___x_1537_);
lean_ctor_set(v___x_1539_, 2, v___x_1536_);
return v___x_1539_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__6(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__5));
v___x_1542_ = l_Lean_stringToMessageData(v___x_1541_);
return v___x_1542_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__8(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__7));
v___x_1545_ = l_Lean_stringToMessageData(v___x_1544_);
return v___x_1545_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__10(void){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__9));
v___x_1548_ = l_Lean_stringToMessageData(v___x_1547_);
return v___x_1548_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__12(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__11));
v___x_1551_ = l_Lean_stringToMessageData(v___x_1550_);
return v___x_1551_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__14(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__13));
v___x_1554_ = l_Lean_stringToMessageData(v___x_1553_);
return v___x_1554_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__16(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__15));
v___x_1557_ = l_Lean_stringToMessageData(v___x_1556_);
return v___x_1557_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__18(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__17));
v___x_1560_ = l_Lean_stringToMessageData(v___x_1559_);
return v___x_1560_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__20(void){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__19));
v___x_1563_ = l_Lean_stringToMessageData(v___x_1562_);
return v___x_1563_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__22(void){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__21));
v___x_1566_ = l_Lean_stringToMessageData(v___x_1565_);
return v___x_1566_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__24(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__23));
v___x_1569_ = l_Lean_stringToMessageData(v___x_1568_);
return v___x_1569_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__26(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__25));
v___x_1572_ = l_Lean_stringToMessageData(v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg(lean_object* v_msg_1573_, lean_object* v_declHint_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v_env_1579_; uint8_t v___x_1580_; 
v___x_1577_ = lean_box(0);
v___x_1578_ = lean_st_ref_get(v___y_1575_);
v_env_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc_ref(v_env_1579_);
lean_dec(v___x_1578_);
v___x_1580_ = l_Lean_Name_isAnonymous(v_declHint_1574_);
if (v___x_1580_ == 0)
{
uint8_t v_isExporting_1581_; 
v_isExporting_1581_ = lean_ctor_get_uint8(v_env_1579_, sizeof(void*)*13);
if (v_isExporting_1581_ == 0)
{
lean_object* v___x_1582_; 
lean_dec_ref(v_env_1579_);
lean_dec(v_declHint_1574_);
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v_msg_1573_);
return v___x_1582_;
}
else
{
lean_object* v___x_1583_; uint8_t v___x_1584_; 
lean_inc_ref(v_env_1579_);
v___x_1583_ = l_Lean_Environment_setExporting(v_env_1579_, v___x_1580_);
lean_inc(v_declHint_1574_);
lean_inc_ref(v___x_1583_);
v___x_1584_ = l_Lean_Environment_contains(v___x_1583_, v_declHint_1574_, v_isExporting_1581_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; 
lean_dec_ref(v___x_1583_);
lean_dec_ref(v_env_1579_);
lean_dec(v_declHint_1574_);
v___x_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1585_, 0, v_msg_1573_);
return v___x_1585_;
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v_c_1591_; lean_object* v___x_1592_; 
v___x_1586_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__1);
v___x_1587_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__4);
v___x_1588_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1583_);
v___x_1589_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1583_);
lean_ctor_set(v___x_1589_, 1, v___x_1586_);
lean_ctor_set(v___x_1589_, 2, v___x_1587_);
lean_ctor_set(v___x_1589_, 3, v___x_1588_);
lean_inc(v_declHint_1574_);
v___x_1590_ = l_Lean_MessageData_ofConstName(v_declHint_1574_, v___x_1580_);
v_c_1591_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1591_, 0, v___x_1589_);
lean_ctor_set(v_c_1591_, 1, v___x_1590_);
v___x_1592_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1583_, v_declHint_1574_);
lean_dec_ref(v___x_1583_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
lean_dec_ref(v_env_1579_);
lean_dec(v_declHint_1574_);
v___x_1593_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__6);
v___x_1594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v_c_1591_);
v___x_1595_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__8);
v___x_1596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1594_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
v___x_1597_ = l_Lean_MessageData_note(v___x_1596_);
v___x_1598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1598_, 0, v_msg_1573_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
return v___x_1599_;
}
else
{
lean_object* v_val_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1653_; 
v_val_1600_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1602_ = v___x_1592_;
v_isShared_1603_ = v_isSharedCheck_1653_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_val_1600_);
lean_dec(v___x_1592_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1653_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v_modules_1605_; lean_object* v_moduleNames_1606_; lean_object* v_mod_1607_; uint8_t v___x_1622_; 
v___x_1604_ = l_Lean_Environment_header(v_env_1579_);
lean_dec_ref(v_env_1579_);
v_modules_1605_ = lean_ctor_get(v___x_1604_, 3);
lean_inc_ref(v_modules_1605_);
v_moduleNames_1606_ = lean_ctor_get(v___x_1604_, 4);
lean_inc_ref(v_moduleNames_1606_);
lean_dec_ref(v___x_1604_);
v_mod_1607_ = lean_array_get(v___x_1577_, v_moduleNames_1606_, v_val_1600_);
lean_dec_ref(v_moduleNames_1606_);
v___x_1622_ = l_Lean_isPrivateName(v_declHint_1574_);
lean_dec(v_declHint_1574_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; uint8_t v___x_1624_; 
v___x_1623_ = lean_array_get_size(v_modules_1605_);
v___x_1624_ = lean_nat_dec_lt(v_val_1600_, v___x_1623_);
if (v___x_1624_ == 0)
{
lean_dec_ref(v_modules_1605_);
lean_dec(v_val_1600_);
goto v___jp_1608_;
}
else
{
lean_object* v___x_1625_; lean_object* v_toImport_1626_; uint8_t v_isExported_1627_; 
v___x_1625_ = lean_array_fget(v_modules_1605_, v_val_1600_);
lean_dec(v_val_1600_);
lean_dec_ref(v_modules_1605_);
v_toImport_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc_ref(v_toImport_1626_);
lean_dec(v___x_1625_);
v_isExported_1627_ = lean_ctor_get_uint8(v_toImport_1626_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1626_);
if (v_isExported_1627_ == 0)
{
goto v___jp_1608_;
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
lean_del_object(v___x_1602_);
v___x_1628_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__16);
v___x_1629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
lean_ctor_set(v___x_1629_, 1, v_c_1591_);
v___x_1630_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__18);
v___x_1631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = l_Lean_MessageData_ofName(v_mod_1607_);
lean_inc_ref(v___x_1632_);
v___x_1633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__20);
v___x_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
lean_ctor_set(v___x_1636_, 1, v___x_1632_);
v___x_1637_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__22);
v___x_1638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1636_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = l_Lean_MessageData_note(v___x_1638_);
v___x_1640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1640_, 0, v_msg_1573_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
return v___x_1641_;
}
}
}
else
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
lean_dec_ref(v_modules_1605_);
lean_del_object(v___x_1602_);
lean_dec(v_val_1600_);
v___x_1642_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__6);
v___x_1643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
lean_ctor_set(v___x_1643_, 1, v_c_1591_);
v___x_1644_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__24);
v___x_1645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1643_);
lean_ctor_set(v___x_1645_, 1, v___x_1644_);
v___x_1646_ = l_Lean_MessageData_ofName(v_mod_1607_);
v___x_1647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1645_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__26, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__26_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__26);
v___x_1649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1647_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
v___x_1650_ = l_Lean_MessageData_note(v___x_1649_);
v___x_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1651_, 0, v_msg_1573_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
return v___x_1652_;
}
v___jp_1608_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1609_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__10);
v___x_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v_c_1591_);
v___x_1611_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__12);
v___x_1612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = l_Lean_MessageData_ofName(v_mod_1607_);
v___x_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___closed__14);
v___x_1616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = l_Lean_MessageData_note(v___x_1616_);
v___x_1618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1618_, 0, v_msg_1573_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set_tag(v___x_1602_, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1618_);
v___x_1620_ = v___x_1602_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1654_; 
lean_dec_ref(v_env_1579_);
lean_dec(v_declHint_1574_);
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v_msg_1573_);
return v___x_1654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg___boxed(lean_object* v_msg_1655_, lean_object* v_declHint_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg(v_msg_1655_, v_declHint_1656_, v___y_1657_);
lean_dec(v___y_1657_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22(lean_object* v_msg_1660_, lean_object* v_declHint_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1677_; 
v___x_1667_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg(v_msg_1660_, v_declHint_1661_, v___y_1665_);
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1677_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1667_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1677_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1672_ = l_Lean_unknownIdentifierMessageTag;
v___x_1673_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
lean_ctor_set(v___x_1673_, 1, v_a_1668_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1673_);
v___x_1675_ = v___x_1670_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22___boxed(lean_object* v_msg_1678_, lean_object* v_declHint_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22(v_msg_1678_, v_declHint_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__23___redArg(lean_object* v_ref_1686_, lean_object* v_msg_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v_toCold_1693_; lean_object* v_currRecDepth_1694_; lean_object* v_ref_1695_; uint16_t v_optionFlags_1696_; uint8_t v_suppressElabErrors_1697_; uint8_t v_checkDeprecated_1698_; uint8_t v_isRecordingDeps_1699_; lean_object* v_ref_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v_toCold_1693_ = lean_ctor_get(v___y_1690_, 0);
v_currRecDepth_1694_ = lean_ctor_get(v___y_1690_, 1);
v_ref_1695_ = lean_ctor_get(v___y_1690_, 2);
v_optionFlags_1696_ = lean_ctor_get_uint16(v___y_1690_, sizeof(void*)*3);
v_suppressElabErrors_1697_ = lean_ctor_get_uint8(v___y_1690_, sizeof(void*)*3 + 2);
v_checkDeprecated_1698_ = lean_ctor_get_uint8(v___y_1690_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1699_ = lean_ctor_get_uint8(v___y_1690_, sizeof(void*)*3 + 4);
v_ref_1700_ = l_Lean_replaceRef(v_ref_1686_, v_ref_1695_);
lean_inc(v_currRecDepth_1694_);
lean_inc_ref(v_toCold_1693_);
v___x_1701_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1701_, 0, v_toCold_1693_);
lean_ctor_set(v___x_1701_, 1, v_currRecDepth_1694_);
lean_ctor_set(v___x_1701_, 2, v_ref_1700_);
lean_ctor_set_uint16(v___x_1701_, sizeof(void*)*3, v_optionFlags_1696_);
lean_ctor_set_uint8(v___x_1701_, sizeof(void*)*3 + 2, v_suppressElabErrors_1697_);
lean_ctor_set_uint8(v___x_1701_, sizeof(void*)*3 + 3, v_checkDeprecated_1698_);
lean_ctor_set_uint8(v___x_1701_, sizeof(void*)*3 + 4, v_isRecordingDeps_1699_);
v___x_1702_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_1687_, v___y_1688_, v___y_1689_, v___x_1701_, v___y_1691_);
lean_dec_ref_known(v___x_1701_, 3);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__23___redArg___boxed(lean_object* v_ref_1703_, lean_object* v_msg_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__23___redArg(v_ref_1703_, v_msg_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v_ref_1703_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17___redArg(lean_object* v_ref_1711_, lean_object* v_msg_1712_, lean_object* v_declHint_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v___x_1719_; lean_object* v_a_1720_; lean_object* v___x_1721_; 
v___x_1719_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22(v_msg_1712_, v_declHint_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref(v___x_1719_);
v___x_1721_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__23___redArg(v_ref_1711_, v_a_1720_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17___redArg___boxed(lean_object* v_ref_1722_, lean_object* v_msg_1723_, lean_object* v_declHint_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17___redArg(v_ref_1722_, v_msg_1723_, v_declHint_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v_ref_1722_);
return v_res_1730_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6___redArg___closed__0));
v___x_1733_ = l_Lean_stringToMessageData(v___x_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6___redArg(lean_object* v_ref_1734_, lean_object* v_constName_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v___x_1741_; uint8_t v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1741_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6___redArg___closed__1);
v___x_1742_ = 0;
lean_inc(v_constName_1735_);
v___x_1743_ = l_Lean_MessageData_ofConstName(v_constName_1735_, v___x_1742_);
v___x_1744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1741_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v___x_1745_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1);
v___x_1746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1744_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
v___x_1747_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17___redArg(v_ref_1734_, v___x_1746_, v_constName_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6___redArg___boxed(lean_object* v_ref_1748_, lean_object* v_constName_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6___redArg(v_ref_1748_, v_constName_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v_ref_1748_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(lean_object* v_constName_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_ref_1762_; lean_object* v___x_1763_; 
v_ref_1762_ = lean_ctor_get(v___y_1759_, 2);
v___x_1763_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6___redArg(v_ref_1762_, v_constName_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg___boxed(lean_object* v_constName_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(lean_object* v_constName_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v___x_1777_; lean_object* v_env_1778_; uint8_t v___x_1779_; lean_object* v___x_1780_; 
v___x_1777_ = lean_st_ref_get(v___y_1775_);
v_env_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc_ref(v_env_1778_);
lean_dec(v___x_1777_);
v___x_1779_ = 0;
lean_inc(v_constName_1771_);
v___x_1780_ = l_Lean_Environment_find_x3f(v_env_1778_, v_constName_1771_, v___x_1779_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
return v___x_1781_;
}
else
{
lean_object* v_val_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec(v_constName_1771_);
v_val_1782_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1780_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_val_1782_);
lean_dec(v___x_1780_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
lean_ctor_set_tag(v___x_1784_, 0);
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_val_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2___boxed(lean_object* v_constName_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_constName_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
return v_res_1796_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1799_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6));
v___x_1800_ = lean_unsigned_to_nat(62u);
v___x_1801_ = lean_unsigned_to_nat(83u);
v___x_1802_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__3___closed__1));
v___x_1803_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__3___closed__0));
v___x_1804_ = l_mkPanicMessageWithDecl(v___x_1803_, v___x_1802_, v___x_1801_, v___x_1800_, v___x_1799_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3(lean_object* v_indName_1805_, uint8_t v___x_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1812_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1809_);
v___x_1813_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_genCtorIdx;
v___x_1814_ = l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(v___x_1812_, v___x_1813_);
lean_dec_ref(v___x_1812_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
lean_dec(v_indName_1805_);
v___x_1815_ = lean_box(0);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
return v___x_1816_;
}
else
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1903_; 
lean_inc(v_indName_1805_);
v___x_1817_ = l_Lean_mkCtorIdxName(v_indName_1805_);
lean_inc(v___x_1817_);
v___x_1818_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v___x_1817_, v___x_1814_, v___y_1810_);
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1821_ = v___x_1818_;
v_isShared_1822_ = v_isSharedCheck_1903_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1818_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1903_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
uint8_t v___x_1823_; 
v___x_1823_ = lean_unbox(v_a_1819_);
lean_dec(v_a_1819_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; 
lean_del_object(v___x_1821_);
lean_inc(v_indName_1805_);
v___x_1824_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_indName_1805_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_a_1825_);
lean_dec_ref_known(v___x_1824_, 1);
if (lean_obj_tag(v_a_1825_) == 5)
{
lean_object* v_val_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1888_; 
v_val_1826_ = lean_ctor_get(v_a_1825_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_a_1825_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1828_ = v_a_1825_;
v_isShared_1829_ = v_isSharedCheck_1888_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_val_1826_);
lean_dec(v_a_1825_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1888_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v_toConstantVal_1830_; lean_object* v_numParams_1831_; lean_object* v_numIndices_1832_; lean_object* v_ctors_1833_; lean_object* v_levelParams_1834_; lean_object* v_type_1835_; lean_object* v___x_1836_; 
v_toConstantVal_1830_ = lean_ctor_get(v_val_1826_, 0);
v_numParams_1831_ = lean_ctor_get(v_val_1826_, 1);
lean_inc(v_numParams_1831_);
v_numIndices_1832_ = lean_ctor_get(v_val_1826_, 2);
lean_inc(v_numIndices_1832_);
v_ctors_1833_ = lean_ctor_get(v_val_1826_, 4);
lean_inc(v_ctors_1833_);
v_levelParams_1834_ = lean_ctor_get(v_toConstantVal_1830_, 1);
lean_inc(v_levelParams_1834_);
v_type_1835_ = lean_ctor_get(v_toConstantVal_1830_, 2);
lean_inc_ref_n(v_type_1835_, 2);
v___x_1836_ = l_Lean_Meta_isPropFormerType(v_type_1835_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1879_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1879_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1879_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
uint8_t v___x_1841_; 
v___x_1841_ = lean_unbox(v_a_1837_);
lean_dec(v_a_1837_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
lean_del_object(v___x_1839_);
lean_inc(v_indName_1805_);
v___x_1842_ = l_Lean_mkCasesOnName(v_indName_1805_);
lean_inc(v___x_1842_);
v___x_1843_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v___x_1842_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1866_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1866_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1866_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1848_ = l_List_lengthTR___redArg(v_levelParams_1834_);
v___x_1849_ = l_Lean_ConstantInfo_levelParams(v_a_1844_);
lean_dec(v_a_1844_);
v___x_1850_ = l_List_lengthTR___redArg(v___x_1849_);
lean_dec(v___x_1849_);
v___x_1851_ = lean_nat_dec_lt(v___x_1848_, v___x_1850_);
lean_dec(v___x_1850_);
lean_dec(v___x_1848_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
lean_dec(v___x_1842_);
lean_dec_ref(v_type_1835_);
lean_dec(v_levelParams_1834_);
lean_dec(v_ctors_1833_);
lean_dec(v_numIndices_1832_);
lean_dec(v_numParams_1831_);
lean_del_object(v___x_1828_);
lean_dec_ref(v_val_1826_);
lean_dec(v___x_1817_);
lean_dec(v_indName_1805_);
v___x_1852_ = lean_box(0);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1852_);
v___x_1854_ = v___x_1846_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___f_1860_; lean_object* v___x_1861_; lean_object* v___x_1863_; 
lean_del_object(v___x_1846_);
v___x_1856_ = lean_box(0);
lean_inc(v_levelParams_1834_);
v___x_1857_ = l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(v_levelParams_1834_, v___x_1856_);
v___x_1858_ = lean_box(v___x_1806_);
v___x_1859_ = lean_box(v___x_1814_);
lean_inc(v_numParams_1831_);
v___f_1860_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__2___boxed), 18, 11);
lean_closure_set(v___f_1860_, 0, v_numParams_1831_);
lean_closure_set(v___f_1860_, 1, v_indName_1805_);
lean_closure_set(v___f_1860_, 2, v___x_1857_);
lean_closure_set(v___f_1860_, 3, v___x_1856_);
lean_closure_set(v___f_1860_, 4, v___x_1858_);
lean_closure_set(v___f_1860_, 5, v___x_1859_);
lean_closure_set(v___f_1860_, 6, v_val_1826_);
lean_closure_set(v___f_1860_, 7, v___x_1842_);
lean_closure_set(v___f_1860_, 8, v_ctors_1833_);
lean_closure_set(v___f_1860_, 9, v___x_1817_);
lean_closure_set(v___f_1860_, 10, v_levelParams_1834_);
v___x_1861_ = lean_nat_add(v_numParams_1831_, v_numIndices_1832_);
lean_dec(v_numIndices_1832_);
lean_dec(v_numParams_1831_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set_tag(v___x_1828_, 1);
lean_ctor_set(v___x_1828_, 0, v___x_1861_);
v___x_1863_ = v___x_1828_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_1835_, v___x_1863_, v___f_1860_, v___x_1806_, v___x_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
return v___x_1864_;
}
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec(v___x_1842_);
lean_dec_ref(v_type_1835_);
lean_dec(v_levelParams_1834_);
lean_dec(v_ctors_1833_);
lean_dec(v_numIndices_1832_);
lean_dec(v_numParams_1831_);
lean_del_object(v___x_1828_);
lean_dec_ref(v_val_1826_);
lean_dec(v___x_1817_);
lean_dec(v_indName_1805_);
v_a_1867_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1843_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1843_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1877_; 
lean_dec_ref(v_type_1835_);
lean_dec(v_levelParams_1834_);
lean_dec(v_ctors_1833_);
lean_dec(v_numIndices_1832_);
lean_dec(v_numParams_1831_);
lean_del_object(v___x_1828_);
lean_dec_ref(v_val_1826_);
lean_dec(v___x_1817_);
lean_dec(v_indName_1805_);
v___x_1875_ = lean_box(0);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1875_);
v___x_1877_ = v___x_1839_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec_ref(v_type_1835_);
lean_dec(v_levelParams_1834_);
lean_dec(v_ctors_1833_);
lean_dec(v_numIndices_1832_);
lean_dec(v_numParams_1831_);
lean_del_object(v___x_1828_);
lean_dec_ref(v_val_1826_);
lean_dec(v___x_1817_);
lean_dec(v_indName_1805_);
v_a_1880_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1836_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1836_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
else
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
lean_dec(v_a_1825_);
lean_dec(v___x_1817_);
lean_dec(v_indName_1805_);
v___x_1889_ = lean_obj_once(&l_Lean_mkCtorIdx___lam__3___closed__2, &l_Lean_mkCtorIdx___lam__3___closed__2_once, _init_l_Lean_mkCtorIdx___lam__3___closed__2);
v___x_1890_ = l_panic___at___00Lean_mkCtorIdx_spec__11(v___x_1889_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
return v___x_1890_;
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec(v___x_1817_);
lean_dec(v_indName_1805_);
v_a_1891_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1824_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1824_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
else
{
lean_object* v___x_1899_; lean_object* v___x_1901_; 
lean_dec(v___x_1817_);
lean_dec(v_indName_1805_);
v___x_1899_ = lean_box(0);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1899_);
v___x_1901_ = v___x_1821_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3___boxed(lean_object* v_indName_1904_, lean_object* v___x_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
uint8_t v___x_23267__boxed_1911_; lean_object* v_res_1912_; 
v___x_23267__boxed_1911_ = lean_unbox(v___x_1905_);
v_res_1912_ = l_Lean_mkCtorIdx___lam__3(v_indName_1904_, v___x_23267__boxed_1911_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
lean_dec(v___y_1909_);
lean_dec_ref(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__4(lean_object* v___x_1913_, lean_object* v_e_1914_){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = l_Lean_indentD(v_e_1914_);
v___x_1916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1913_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5(lean_object* v___f_1917_, lean_object* v___f_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Lean_Meta_mapErrorImp___redArg(v___f_1917_, v___f_1918_, v___y_1919_, v___y_1920_, v___y_1921_, v___y_1922_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1924_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1924_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
v_a_1933_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1924_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1924_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5___boxed(lean_object* v___f_1941_, lean_object* v___f_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_mkCtorIdx___lam__5(v___f_1941_, v___f_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0(lean_object* v___y_1949_, uint8_t v_isExporting_1950_, lean_object* v___x_1951_, lean_object* v___y_1952_, lean_object* v___x_1953_, lean_object* v_a_x3f_1954_){
_start:
{
lean_object* v___x_1956_; lean_object* v_env_1957_; lean_object* v_nextMacroScope_1958_; lean_object* v_ngen_1959_; lean_object* v_auxDeclNGen_1960_; lean_object* v_traceState_1961_; lean_object* v_recordedDeps_1962_; lean_object* v_messages_1963_; lean_object* v_infoState_1964_; lean_object* v_snapshotTasks_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1990_; 
v___x_1956_ = lean_st_ref_take(v___y_1949_);
v_env_1957_ = lean_ctor_get(v___x_1956_, 0);
v_nextMacroScope_1958_ = lean_ctor_get(v___x_1956_, 1);
v_ngen_1959_ = lean_ctor_get(v___x_1956_, 2);
v_auxDeclNGen_1960_ = lean_ctor_get(v___x_1956_, 3);
v_traceState_1961_ = lean_ctor_get(v___x_1956_, 4);
v_recordedDeps_1962_ = lean_ctor_get(v___x_1956_, 6);
v_messages_1963_ = lean_ctor_get(v___x_1956_, 7);
v_infoState_1964_ = lean_ctor_get(v___x_1956_, 8);
v_snapshotTasks_1965_ = lean_ctor_get(v___x_1956_, 9);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1990_ == 0)
{
lean_object* v_unused_1991_; 
v_unused_1991_ = lean_ctor_get(v___x_1956_, 5);
lean_dec(v_unused_1991_);
v___x_1967_ = v___x_1956_;
v_isShared_1968_ = v_isSharedCheck_1990_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_snapshotTasks_1965_);
lean_inc(v_infoState_1964_);
lean_inc(v_messages_1963_);
lean_inc(v_recordedDeps_1962_);
lean_inc(v_traceState_1961_);
lean_inc(v_auxDeclNGen_1960_);
lean_inc(v_ngen_1959_);
lean_inc(v_nextMacroScope_1958_);
lean_inc(v_env_1957_);
lean_dec(v___x_1956_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1990_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1969_ = l_Lean_Environment_setExporting(v_env_1957_, v_isExporting_1950_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 5, v___x_1951_);
lean_ctor_set(v___x_1967_, 0, v___x_1969_);
v___x_1971_ = v___x_1967_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_nextMacroScope_1958_);
lean_ctor_set(v_reuseFailAlloc_1989_, 2, v_ngen_1959_);
lean_ctor_set(v_reuseFailAlloc_1989_, 3, v_auxDeclNGen_1960_);
lean_ctor_set(v_reuseFailAlloc_1989_, 4, v_traceState_1961_);
lean_ctor_set(v_reuseFailAlloc_1989_, 5, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_1989_, 6, v_recordedDeps_1962_);
lean_ctor_set(v_reuseFailAlloc_1989_, 7, v_messages_1963_);
lean_ctor_set(v_reuseFailAlloc_1989_, 8, v_infoState_1964_);
lean_ctor_set(v_reuseFailAlloc_1989_, 9, v_snapshotTasks_1965_);
v___x_1971_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v_mctx_1974_; lean_object* v_zetaDeltaFVarIds_1975_; lean_object* v_postponed_1976_; lean_object* v_diag_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1987_; 
v___x_1972_ = lean_st_ref_put(v___y_1949_, v___x_1971_);
v___x_1973_ = lean_st_ref_take(v___y_1952_);
v_mctx_1974_ = lean_ctor_get(v___x_1973_, 0);
v_zetaDeltaFVarIds_1975_ = lean_ctor_get(v___x_1973_, 2);
v_postponed_1976_ = lean_ctor_get(v___x_1973_, 3);
v_diag_1977_ = lean_ctor_get(v___x_1973_, 4);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1987_ == 0)
{
lean_object* v_unused_1988_; 
v_unused_1988_ = lean_ctor_get(v___x_1973_, 1);
lean_dec(v_unused_1988_);
v___x_1979_ = v___x_1973_;
v_isShared_1980_ = v_isSharedCheck_1987_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_diag_1977_);
lean_inc(v_postponed_1976_);
lean_inc(v_zetaDeltaFVarIds_1975_);
lean_inc(v_mctx_1974_);
lean_dec(v___x_1973_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1987_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; lean_object* v___x_1983_; 
v___x_1981_ = lean_box(0);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 1, v___x_1953_);
v___x_1983_ = v___x_1979_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_mctx_1974_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_1986_, 2, v_zetaDeltaFVarIds_1975_);
lean_ctor_set(v_reuseFailAlloc_1986_, 3, v_postponed_1976_);
lean_ctor_set(v_reuseFailAlloc_1986_, 4, v_diag_1977_);
v___x_1983_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = lean_st_ref_put(v___y_1952_, v___x_1983_);
v___x_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1981_);
return v___x_1985_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0___boxed(lean_object* v___y_1992_, lean_object* v_isExporting_1993_, lean_object* v___x_1994_, lean_object* v___y_1995_, lean_object* v___x_1996_, lean_object* v_a_x3f_1997_, lean_object* v___y_1998_){
_start:
{
uint8_t v_isExporting_boxed_1999_; lean_object* v_res_2000_; 
v_isExporting_boxed_1999_ = lean_unbox(v_isExporting_1993_);
v_res_2000_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0(v___y_1992_, v_isExporting_boxed_1999_, v___x_1994_, v___y_1995_, v___x_1996_, v_a_x3f_1997_);
lean_dec(v_a_x3f_1997_);
lean_dec(v___y_1995_);
lean_dec(v___y_1992_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(lean_object* v_x_2001_, uint8_t v_isExporting_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v___x_2008_; lean_object* v_env_2009_; lean_object* v___x_2010_; uint8_t v_isModule_2011_; 
v___x_2008_ = lean_st_ref_get(v___y_2006_);
v_env_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc_ref(v_env_2009_);
lean_dec(v___x_2008_);
v___x_2010_ = l_Lean_Environment_header(v_env_2009_);
v_isModule_2011_ = lean_ctor_get_uint8(v___x_2010_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2010_);
if (v_isModule_2011_ == 0)
{
lean_object* v___x_2012_; 
lean_dec_ref(v_env_2009_);
lean_inc(v___y_2006_);
lean_inc_ref(v___y_2005_);
lean_inc(v___y_2004_);
lean_inc_ref(v___y_2003_);
v___x_2012_ = lean_apply_5(v_x_2001_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, lean_box(0));
return v___x_2012_;
}
else
{
uint8_t v_isExporting_2013_; 
v_isExporting_2013_ = lean_ctor_get_uint8(v_env_2009_, sizeof(void*)*13);
lean_dec_ref(v_env_2009_);
if (v_isExporting_2002_ == 0)
{
if (v_isExporting_2013_ == 0)
{
lean_object* v___x_2080_; 
lean_inc(v___y_2006_);
lean_inc_ref(v___y_2005_);
lean_inc(v___y_2004_);
lean_inc_ref(v___y_2003_);
v___x_2080_ = lean_apply_5(v_x_2001_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, lean_box(0));
return v___x_2080_;
}
else
{
goto v___jp_2014_;
}
}
else
{
if (v_isExporting_2013_ == 0)
{
goto v___jp_2014_;
}
else
{
lean_object* v___x_2081_; 
lean_inc(v___y_2006_);
lean_inc_ref(v___y_2005_);
lean_inc(v___y_2004_);
lean_inc_ref(v___y_2003_);
v___x_2081_ = lean_apply_5(v_x_2001_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, lean_box(0));
return v___x_2081_;
}
}
v___jp_2014_:
{
lean_object* v___x_2015_; lean_object* v_env_2016_; lean_object* v_nextMacroScope_2017_; lean_object* v_ngen_2018_; lean_object* v_auxDeclNGen_2019_; lean_object* v_traceState_2020_; lean_object* v_recordedDeps_2021_; lean_object* v_messages_2022_; lean_object* v_infoState_2023_; lean_object* v_snapshotTasks_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2078_; 
v___x_2015_ = lean_st_ref_take(v___y_2006_);
v_env_2016_ = lean_ctor_get(v___x_2015_, 0);
v_nextMacroScope_2017_ = lean_ctor_get(v___x_2015_, 1);
v_ngen_2018_ = lean_ctor_get(v___x_2015_, 2);
v_auxDeclNGen_2019_ = lean_ctor_get(v___x_2015_, 3);
v_traceState_2020_ = lean_ctor_get(v___x_2015_, 4);
v_recordedDeps_2021_ = lean_ctor_get(v___x_2015_, 6);
v_messages_2022_ = lean_ctor_get(v___x_2015_, 7);
v_infoState_2023_ = lean_ctor_get(v___x_2015_, 8);
v_snapshotTasks_2024_ = lean_ctor_get(v___x_2015_, 9);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2078_ == 0)
{
lean_object* v_unused_2079_; 
v_unused_2079_ = lean_ctor_get(v___x_2015_, 5);
lean_dec(v_unused_2079_);
v___x_2026_ = v___x_2015_;
v_isShared_2027_ = v_isSharedCheck_2078_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_snapshotTasks_2024_);
lean_inc(v_infoState_2023_);
lean_inc(v_messages_2022_);
lean_inc(v_recordedDeps_2021_);
lean_inc(v_traceState_2020_);
lean_inc(v_auxDeclNGen_2019_);
lean_inc(v_ngen_2018_);
lean_inc(v_nextMacroScope_2017_);
lean_inc(v_env_2016_);
lean_dec(v___x_2015_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2078_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2028_ = l_Lean_Environment_setExporting(v_env_2016_, v_isExporting_2002_);
v___x_2029_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 5, v___x_2029_);
lean_ctor_set(v___x_2026_, 0, v___x_2028_);
v___x_2031_ = v___x_2026_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2028_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_nextMacroScope_2017_);
lean_ctor_set(v_reuseFailAlloc_2077_, 2, v_ngen_2018_);
lean_ctor_set(v_reuseFailAlloc_2077_, 3, v_auxDeclNGen_2019_);
lean_ctor_set(v_reuseFailAlloc_2077_, 4, v_traceState_2020_);
lean_ctor_set(v_reuseFailAlloc_2077_, 5, v___x_2029_);
lean_ctor_set(v_reuseFailAlloc_2077_, 6, v_recordedDeps_2021_);
lean_ctor_set(v_reuseFailAlloc_2077_, 7, v_messages_2022_);
lean_ctor_set(v_reuseFailAlloc_2077_, 8, v_infoState_2023_);
lean_ctor_set(v_reuseFailAlloc_2077_, 9, v_snapshotTasks_2024_);
v___x_2031_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v_mctx_2034_; lean_object* v_zetaDeltaFVarIds_2035_; lean_object* v_postponed_2036_; lean_object* v_diag_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2075_; 
v___x_2032_ = lean_st_ref_put(v___y_2006_, v___x_2031_);
v___x_2033_ = lean_st_ref_take(v___y_2004_);
v_mctx_2034_ = lean_ctor_get(v___x_2033_, 0);
v_zetaDeltaFVarIds_2035_ = lean_ctor_get(v___x_2033_, 2);
v_postponed_2036_ = lean_ctor_get(v___x_2033_, 3);
v_diag_2037_ = lean_ctor_get(v___x_2033_, 4);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; 
v_unused_2076_ = lean_ctor_get(v___x_2033_, 1);
lean_dec(v_unused_2076_);
v___x_2039_ = v___x_2033_;
v_isShared_2040_ = v_isSharedCheck_2075_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_diag_2037_);
lean_inc(v_postponed_2036_);
lean_inc(v_zetaDeltaFVarIds_2035_);
lean_inc(v_mctx_2034_);
lean_dec(v___x_2033_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2075_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2041_; lean_object* v___x_2043_; 
v___x_2041_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__6, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__6_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__6);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 1, v___x_2041_);
v___x_2043_ = v___x_2039_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_mctx_2034_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_zetaDeltaFVarIds_2035_);
lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_postponed_2036_);
lean_ctor_set(v_reuseFailAlloc_2074_, 4, v_diag_2037_);
v___x_2043_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2044_; lean_object* v_r_2045_; 
v___x_2044_ = lean_st_ref_put(v___y_2004_, v___x_2043_);
lean_inc(v___y_2006_);
lean_inc_ref(v___y_2005_);
lean_inc(v___y_2004_);
lean_inc_ref(v___y_2003_);
v_r_2045_ = lean_apply_5(v_x_2001_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, lean_box(0));
if (lean_obj_tag(v_r_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2062_; 
v_a_2046_ = lean_ctor_get(v_r_2045_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v_r_2045_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2048_ = v_r_2045_;
v_isShared_2049_ = v_isSharedCheck_2062_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v_r_2045_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2062_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
lean_inc(v_a_2046_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set_tag(v___x_2048_, 1);
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_object* v___x_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
v___x_2052_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0(v___y_2006_, v_isExporting_2013_, v___x_2029_, v___y_2004_, v___x_2041_, v___x_2051_);
lean_dec_ref(v___x_2051_);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2059_ == 0)
{
lean_object* v_unused_2060_; 
v_unused_2060_ = lean_ctor_get(v___x_2052_, 0);
lean_dec(v_unused_2060_);
v___x_2054_ = v___x_2052_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_dec(v___x_2052_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v_a_2046_);
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2046_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
v_a_2063_ = lean_ctor_get(v_r_2045_, 0);
lean_inc(v_a_2063_);
lean_dec_ref_known(v_r_2045_, 1);
v___x_2064_ = lean_box(0);
v___x_2065_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0(v___y_2006_, v_isExporting_2013_, v___x_2029_, v___y_2004_, v___x_2041_, v___x_2064_);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2072_ == 0)
{
lean_object* v_unused_2073_; 
v_unused_2073_ = lean_ctor_get(v___x_2065_, 0);
lean_dec(v_unused_2073_);
v___x_2067_ = v___x_2065_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_dec(v___x_2065_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
lean_ctor_set_tag(v___x_2067_, 1);
lean_ctor_set(v___x_2067_, 0, v_a_2063_);
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2063_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___boxed(lean_object* v_x_2082_, lean_object* v_isExporting_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
uint8_t v_isExporting_boxed_2089_; lean_object* v_res_2090_; 
v_isExporting_boxed_2089_ = lean_unbox(v_isExporting_2083_);
v_res_2090_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(v_x_2082_, v_isExporting_boxed_2089_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
return v_res_2090_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___closed__1(void){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = ((lean_object*)(l_Lean_mkCtorIdx___closed__0));
v___x_2093_ = l_Lean_stringToMessageData(v___x_2092_);
return v___x_2093_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___closed__3(void){
_start:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = ((lean_object*)(l_Lean_mkCtorIdx___closed__2));
v___x_2096_ = l_Lean_stringToMessageData(v___x_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx(lean_object* v_indName_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v___x_2103_; uint8_t v___x_2104_; lean_object* v___x_2105_; lean_object* v___f_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___f_2111_; lean_object* v___f_2112_; uint8_t v___x_2113_; 
v___x_2103_ = lean_obj_once(&l_Lean_mkCtorIdx___closed__1, &l_Lean_mkCtorIdx___closed__1_once, _init_l_Lean_mkCtorIdx___closed__1);
v___x_2104_ = 0;
v___x_2105_ = lean_box(v___x_2104_);
lean_inc_n(v_indName_2097_, 2);
v___f_2106_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__3___boxed), 7, 2);
lean_closure_set(v___f_2106_, 0, v_indName_2097_);
lean_closure_set(v___f_2106_, 1, v___x_2105_);
v___x_2107_ = l_Lean_MessageData_ofConstName(v_indName_2097_, v___x_2104_);
v___x_2108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2103_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
v___x_2109_ = lean_obj_once(&l_Lean_mkCtorIdx___closed__3, &l_Lean_mkCtorIdx___closed__3_once, _init_l_Lean_mkCtorIdx___closed__3);
v___x_2110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2108_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___f_2111_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__4), 2, 1);
lean_closure_set(v___f_2111_, 0, v___x_2110_);
v___f_2112_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__5___boxed), 7, 2);
lean_closure_set(v___f_2112_, 0, v___f_2106_);
lean_closure_set(v___f_2112_, 1, v___f_2111_);
v___x_2113_ = l_Lean_isPrivateName(v_indName_2097_);
lean_dec(v_indName_2097_);
if (v___x_2113_ == 0)
{
uint8_t v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = 1;
v___x_2115_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(v___f_2112_, v___x_2114_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
return v___x_2115_;
}
else
{
lean_object* v___x_2116_; 
v___x_2116_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(v___f_2112_, v___x_2104_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
return v___x_2116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___boxed(lean_object* v_indName_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_mkCtorIdx(v_indName_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(uint8_t v___x_2124_, lean_object* v___x_2125_, lean_object* v_as_2126_, lean_object* v_as_x27_2127_, lean_object* v_b_2128_, lean_object* v_a_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_2124_, v___x_2125_, v_as_x27_2127_, v_b_2128_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___boxed(lean_object* v___x_2136_, lean_object* v___x_2137_, lean_object* v_as_2138_, lean_object* v_as_x27_2139_, lean_object* v_b_2140_, lean_object* v_a_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
uint8_t v___x_23798__boxed_2147_; lean_object* v_res_2148_; 
v___x_23798__boxed_2147_ = lean_unbox(v___x_2136_);
v_res_2148_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(v___x_23798__boxed_2147_, v___x_2137_, v_as_2138_, v_as_x27_2139_, v_b_2140_, v_a_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v_as_x27_2139_);
lean_dec(v_as_2138_);
lean_dec_ref(v___x_2137_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10(lean_object* v_00_u03b1_2149_, lean_object* v_name_2150_, uint8_t v_bi_2151_, lean_object* v_type_2152_, lean_object* v_k_2153_, uint8_t v_kind_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_2150_, v_bi_2151_, v_type_2152_, v_k_2153_, v_kind_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2161_, lean_object* v_name_2162_, lean_object* v_bi_2163_, lean_object* v_type_2164_, lean_object* v_k_2165_, lean_object* v_kind_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
uint8_t v_bi_boxed_2172_; uint8_t v_kind_boxed_2173_; lean_object* v_res_2174_; 
v_bi_boxed_2172_ = lean_unbox(v_bi_2163_);
v_kind_boxed_2173_ = lean_unbox(v_kind_2166_);
v_res_2174_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10(v_00_u03b1_2161_, v_name_2162_, v_bi_boxed_2172_, v_type_2164_, v_k_2165_, v_kind_boxed_2173_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7(lean_object* v_00_u03b1_2175_, lean_object* v_name_2176_, lean_object* v_type_2177_, lean_object* v_k_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v_name_2176_, v_type_2177_, v_k_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___boxed(lean_object* v_00_u03b1_2185_, lean_object* v_name_2186_, lean_object* v_type_2187_, lean_object* v_k_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7(v_00_u03b1_2185_, v_name_2186_, v_type_2187_, v_k_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16(lean_object* v_00_u03b1_2195_, lean_object* v_bs_2196_, lean_object* v_k_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v___x_2203_; 
v___x_2203_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(v_bs_2196_, v_k_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___boxed(lean_object* v_00_u03b1_2204_, lean_object* v_bs_2205_, lean_object* v_k_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16(v_00_u03b1_2204_, v_bs_2205_, v_k_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec_ref(v_bs_2205_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10(lean_object* v_00_u03b1_2213_, lean_object* v_bs_2214_, lean_object* v_k_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(v_bs_2214_, v_k_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___boxed(lean_object* v_00_u03b1_2222_, lean_object* v_bs_2223_, lean_object* v_k_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10(v_00_u03b1_2222_, v_bs_2223_, v_k_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12(lean_object* v_00_u03b1_2231_, lean_object* v_x_2232_, uint8_t v_isExporting_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v___x_2239_; 
v___x_2239_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(v_x_2232_, v_isExporting_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___boxed(lean_object* v_00_u03b1_2240_, lean_object* v_x_2241_, lean_object* v_isExporting_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
uint8_t v_isExporting_boxed_2248_; lean_object* v_res_2249_; 
v_isExporting_boxed_2248_ = lean_unbox(v_isExporting_2242_);
v_res_2249_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12(v_00_u03b1_2240_, v_x_2241_, v_isExporting_boxed_2248_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(lean_object* v_00_u03b1_2250_, lean_object* v_constName_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v___x_2257_; 
v___x_2257_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2258_, lean_object* v_constName_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(v_00_u03b1_2258_, v_constName_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(lean_object* v_00_u03b1_2266_, lean_object* v_msg_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2274_, lean_object* v_msg_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(v_00_u03b1_2274_, v_msg_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13(lean_object* v_env_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(v_env_2282_, v___y_2284_, v___y_2286_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___boxed(lean_object* v_env_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13(v_env_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6(lean_object* v_00_u03b1_2296_, lean_object* v_ref_2297_, lean_object* v_constName_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6___redArg(v_ref_2297_, v_constName_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6___boxed(lean_object* v_00_u03b1_2305_, lean_object* v_ref_2306_, lean_object* v_constName_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6(v_00_u03b1_2305_, v_ref_2306_, v_constName_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v_ref_2306_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17(lean_object* v_00_u03b1_2314_, lean_object* v_ref_2315_, lean_object* v_msg_2316_, lean_object* v_declHint_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17___redArg(v_ref_2315_, v_msg_2316_, v_declHint_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17___boxed(lean_object* v_00_u03b1_2324_, lean_object* v_ref_2325_, lean_object* v_msg_2326_, lean_object* v_declHint_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17(v_00_u03b1_2324_, v_ref_2325_, v_msg_2326_, v_declHint_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v_ref_2325_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23(lean_object* v_msg_2334_, lean_object* v_declHint_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___redArg(v_msg_2334_, v_declHint_2335_, v___y_2339_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23___boxed(lean_object* v_msg_2342_, lean_object* v_declHint_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__22_spec__23(v_msg_2342_, v_declHint_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__23(lean_object* v_00_u03b1_2350_, lean_object* v_ref_2351_, lean_object* v_msg_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__23___redArg(v_ref_2351_, v_msg_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__23___boxed(lean_object* v_00_u03b1_2359_, lean_object* v_ref_2360_, lean_object* v_msg_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__6_spec__17_spec__23(v_00_u03b1_2359_, v_ref_2360_, v_msg_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v_ref_2360_);
return v_res_2367_;
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
