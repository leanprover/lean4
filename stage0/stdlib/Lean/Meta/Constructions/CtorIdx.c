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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__19 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__19_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__20;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__21 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__21_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__22;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__23 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__23_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__24;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__25 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__25_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__26;
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
lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_74_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_75_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_76_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_77_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v___x_74_, v___x_75_, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_78_;
v_res_78_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
stack->m_obj
 = v_res_78_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4____boxed(lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdxName(lean_object* v_indName_82_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = ((lean_object*)(l_Lean_mkCtorIdxName___closed__0));
v___x_84_ = l_Lean_Name_str___override(v_indName_82_, v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImplName(lean_object* v_indName_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = l_Lean_mkCtorIdxName(v_indName_86_);
v___x_88_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImplName___closed__0));
v___x_89_ = l_Lean_Name_str___override(v___x_87_, v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdxCore_x3f(lean_object* v_env_90_, lean_object* v_declName_91_){
_start:
{
if (lean_obj_tag(v_declName_91_) == 1)
{
lean_object* v_pre_92_; lean_object* v_str_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v_pre_92_ = lean_ctor_get(v_declName_91_, 0);
lean_inc(v_pre_92_);
v_str_93_ = lean_ctor_get(v_declName_91_, 1);
lean_inc_ref(v_str_93_);
lean_dec_ref_known(v_declName_91_, 2);
v___x_94_ = ((lean_object*)(l_Lean_mkCtorIdxName___closed__0));
v___x_95_ = lean_string_dec_eq(v_str_93_, v___x_94_);
lean_dec_ref(v_str_93_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; 
lean_dec(v_pre_92_);
lean_dec_ref(v_env_90_);
v___x_96_ = lean_box(0);
return v___x_96_;
}
else
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_isInductiveCore_x3f(v_env_90_, v_pre_92_);
return v___x_97_;
}
}
else
{
lean_object* v___x_98_; 
lean_dec(v_declName_91_);
lean_dec_ref(v_env_90_);
v___x_98_ = lean_box(0);
return v___x_98_;
}
}
}
lean_object* l_Lean_isCtorIdx_x3f___redArg(lean_object* v_declName_99_, lean_object* v_a_100_){
_start:
{
lean_object* v___x_102_; lean_object* v_env_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_102_ = lean_st_ref_get(v_a_100_);
v_env_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc_ref(v_env_103_);
lean_dec(v___x_102_);
v___x_104_ = l_Lean_isCtorIdxCore_x3f(v_env_103_, v_declName_99_);
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT void l_Lean_isCtorIdx_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_99_ = stack[0].m_obj;
lean_object* v_a_100_ = stack[1].m_obj;
lean_object* v_res_106_;
v_res_106_ = l_Lean_isCtorIdx_x3f___redArg(v_declName_99_, v_a_100_);
stack->m_obj
 = v_res_106_;
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___redArg___boxed(lean_object* v_declName_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_isCtorIdx_x3f___redArg(v_declName_107_, v_a_108_);
lean_dec(v_a_108_);
return v_res_110_;
}
}
lean_object* l_Lean_isCtorIdx_x3f(lean_object* v_declName_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_isCtorIdx_x3f___redArg(v_declName_111_, v_a_115_);
return v___x_117_;
}
}
LEAN_EXPORT void l_Lean_isCtorIdx_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_111_ = stack[0].m_obj;
lean_object* v_a_112_ = stack[1].m_obj;
lean_object* v_a_113_ = stack[2].m_obj;
lean_object* v_a_114_ = stack[3].m_obj;
lean_object* v_a_115_ = stack[4].m_obj;
lean_object* v_res_118_;
v_res_118_ = l_Lean_isCtorIdx_x3f(v_declName_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
stack->m_obj
 = v_res_118_;
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___boxed(lean_object* v_declName_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_isCtorIdx_x3f(v_declName_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_);
lean_dec(v_a_123_);
lean_dec_ref(v_a_122_);
lean_dec(v_a_121_);
lean_dec_ref(v_a_120_);
return v_res_125_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0(lean_object* v_k_126_, lean_object* v_b_127_, lean_object* v_c_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; 
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
lean_inc(v___y_130_);
lean_inc_ref(v___y_129_);
v___x_134_ = lean_apply_7(v_k_126_, v_b_127_, v_c_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, lean_box(0));
return v___x_134_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_126_ = stack[0].m_obj;
lean_object* v_b_127_ = stack[1].m_obj;
lean_object* v_c_128_ = stack[2].m_obj;
lean_object* v___y_129_ = stack[3].m_obj;
lean_object* v___y_130_ = stack[4].m_obj;
lean_object* v___y_131_ = stack[5].m_obj;
lean_object* v___y_132_ = stack[6].m_obj;
lean_object* v_res_135_;
v_res_135_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0(v_k_126_, v_b_127_, v_c_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_);
stack->m_obj
 = v_res_135_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0___boxed(lean_object* v_k_136_, lean_object* v_b_137_, lean_object* v_c_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0(v_k_136_, v_b_137_, v_c_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
return v_res_144_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg(lean_object* v_type_145_, lean_object* v_k_146_, uint8_t v_cleanupAnnotations_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___f_153_; uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___f_153_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_153_, 0, v_k_146_);
v___x_154_ = 0;
v___x_155_ = lean_box(0);
v___x_156_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_154_, v___x_155_, v_type_145_, v___f_153_, v_cleanupAnnotations_147_, v___x_154_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___x_156_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
v_a_165_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_156_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_156_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_145_ = stack[0].m_obj;
lean_object* v_k_146_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_147_ = stack[2].m_num;
lean_object* v___y_148_ = stack[3].m_obj;
lean_object* v___y_149_ = stack[4].m_obj;
lean_object* v___y_150_ = stack[5].m_obj;
lean_object* v___y_151_ = stack[6].m_obj;
lean_object* v_res_173_;
v_res_173_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg(v_type_145_, v_k_146_, v_cleanupAnnotations_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
stack->m_obj
 = v_res_173_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___boxed(lean_object* v_type_174_, lean_object* v_k_175_, lean_object* v_cleanupAnnotations_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_182_; lean_object* v_res_183_; 
v_cleanupAnnotations_boxed_182_ = lean_unbox(v_cleanupAnnotations_176_);
v_res_183_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg(v_type_174_, v_k_175_, v_cleanupAnnotations_boxed_182_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
return v_res_183_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0(lean_object* v_00_u03b1_184_, lean_object* v_type_185_, lean_object* v_k_186_, uint8_t v_cleanupAnnotations_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg(v_type_185_, v_k_186_, v_cleanupAnnotations_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
return v___x_193_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_185_ = stack[1].m_obj;
lean_object* v_k_186_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_187_ = stack[3].m_num;
lean_object* v___y_188_ = stack[4].m_obj;
lean_object* v___y_189_ = stack[5].m_obj;
lean_object* v___y_190_ = stack[6].m_obj;
lean_object* v___y_191_ = stack[7].m_obj;
lean_object* v_res_194_;
v_res_194_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0(lean_box(0), v_type_185_, v_k_186_, v_cleanupAnnotations_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
stack->m_obj
 = v_res_194_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___boxed(lean_object* v_00_u03b1_195_, lean_object* v_type_196_, lean_object* v_k_197_, lean_object* v_cleanupAnnotations_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_204_; lean_object* v_res_205_; 
v_cleanupAnnotations_boxed_204_ = lean_unbox(v_cleanupAnnotations_198_);
v_res_205_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0(v_00_u03b1_195_, v_type_196_, v_k_197_, v_cleanupAnnotations_boxed_204_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
return v_res_205_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0(lean_object* v___x_209_, lean_object* v_args_210_, lean_object* v_x_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v_discr_220_; lean_object* v___x_221_; 
v___x_217_ = lean_array_get_size(v_args_210_);
v___x_218_ = lean_unsigned_to_nat(1u);
v___x_219_ = lean_nat_sub(v___x_217_, v___x_218_);
v_discr_220_ = lean_array_get_borrowed(v___x_209_, v_args_210_, v___x_219_);
lean_dec(v___x_219_);
lean_inc(v___y_215_);
lean_inc_ref(v___y_214_);
lean_inc(v___y_213_);
lean_inc_ref(v___y_212_);
lean_inc(v_discr_220_);
v___x_221_ = lean_infer_type(v_discr_220_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; lean_object* v___x_223_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc_n(v_a_222_, 2);
lean_dec_ref_known(v___x_221_, 1);
v___x_223_ = l_Lean_Meta_getLevel(v_a_222_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; uint8_t v___x_231_; uint8_t v___x_232_; lean_object* v___x_233_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_a_224_);
lean_dec_ref_known(v___x_223_, 1);
v___x_225_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___closed__1));
v___x_226_ = lean_box(0);
v___x_227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_227_, 0, v_a_224_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = l_Lean_mkConst(v___x_225_, v___x_227_);
lean_inc(v_discr_220_);
v___x_229_ = l_Lean_mkAppB(v___x_228_, v_a_222_, v_discr_220_);
v___x_230_ = 0;
v___x_231_ = 1;
v___x_232_ = 1;
v___x_233_ = l_Lean_Meta_mkLambdaFVars(v_args_210_, v___x_229_, v___x_230_, v___x_231_, v___x_230_, v___x_231_, v___x_232_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
return v___x_233_;
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
lean_dec(v_a_222_);
v_a_234_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_223_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_223_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
else
{
return v___x_221_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_209_ = stack[0].m_obj;
lean_object* v_args_210_ = stack[1].m_obj;
lean_object* v_x_211_ = stack[2].m_obj;
lean_object* v___y_212_ = stack[3].m_obj;
lean_object* v___y_213_ = stack[4].m_obj;
lean_object* v___y_214_ = stack[5].m_obj;
lean_object* v___y_215_ = stack[6].m_obj;
lean_object* v_res_242_;
v_res_242_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0(v___x_209_, v_args_210_, v_x_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
stack->m_obj
 = v_res_242_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___boxed(lean_object* v___x_243_, lean_object* v_args_244_, lean_object* v_x_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0(v___x_243_, v_args_244_, v_x_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec_ref(v_x_245_);
lean_dec_ref(v_args_244_);
lean_dec_ref(v___x_243_);
return v_res_251_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__0(void){
_start:
{
lean_object* v___x_252_; lean_object* v___f_253_; 
v___x_252_ = l_Lean_instInhabitedExpr;
v___f_253_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___lam__0___boxed), 8, 1);
lean_closure_set(v___f_253_, 0, v___x_252_);
return v___f_253_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1(void){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_254_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
return v___x_258_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__2);
v___x_260_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
lean_ctor_set(v___x_260_, 2, v___x_259_);
lean_ctor_set(v___x_260_, 3, v___x_259_);
lean_ctor_set(v___x_260_, 4, v___x_259_);
lean_ctor_set(v___x_260_, 5, v___x_259_);
return v___x_260_;
}
}
lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl(lean_object* v_indName_261_, lean_object* v_levelParams_262_, lean_object* v_declType_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
lean_object* v___f_269_; lean_object* v_implName_270_; uint8_t v___x_271_; lean_object* v___x_272_; 
v___f_269_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__0, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__0_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__0);
lean_inc(v_indName_261_);
v_implName_270_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImplName(v_indName_261_);
v___x_271_ = 0;
lean_inc_ref(v_declType_263_);
v___x_272_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg(v_declType_263_, v___f_269_, v___x_271_, v_a_264_, v_a_265_, v_a_266_, v_a_267_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___y_282_; lean_object* v___y_283_; lean_object* v___y_284_; lean_object* v___y_285_; lean_object* v___x_314_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_a_273_);
lean_dec_ref_known(v___x_272_, 1);
lean_inc_n(v_implName_270_, 2);
v___x_274_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_274_, 0, v_implName_270_);
lean_ctor_set(v___x_274_, 1, v_levelParams_262_);
lean_ctor_set(v___x_274_, 2, v_declType_263_);
v___x_275_ = lean_box(0);
v___x_276_ = 0;
v___x_277_ = lean_box(0);
v___x_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_278_, 0, v_implName_270_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_279_, 0, v___x_274_);
lean_ctor_set(v___x_279_, 1, v_a_273_);
lean_ctor_set(v___x_279_, 2, v___x_275_);
lean_ctor_set(v___x_279_, 3, v___x_278_);
lean_ctor_set_uint8(v___x_279_, sizeof(void*)*4, v___x_276_);
v___x_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_inc_ref(v___x_280_);
v___x_314_ = l_Lean_addDecl(v___x_280_, v___x_271_, v_a_266_, v_a_267_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v___x_315_; lean_object* v_env_316_; lean_object* v_nextMacroScope_317_; lean_object* v_ngen_318_; lean_object* v_auxDeclNGen_319_; lean_object* v_traceState_320_; lean_object* v_recordedDeps_321_; lean_object* v_messages_322_; lean_object* v_infoState_323_; lean_object* v_snapshotTasks_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_420_; 
lean_dec_ref_known(v___x_314_, 1);
v___x_315_ = lean_st_ref_take(v_a_267_);
v_env_316_ = lean_ctor_get(v___x_315_, 0);
v_nextMacroScope_317_ = lean_ctor_get(v___x_315_, 1);
v_ngen_318_ = lean_ctor_get(v___x_315_, 2);
v_auxDeclNGen_319_ = lean_ctor_get(v___x_315_, 3);
v_traceState_320_ = lean_ctor_get(v___x_315_, 4);
v_recordedDeps_321_ = lean_ctor_get(v___x_315_, 6);
v_messages_322_ = lean_ctor_get(v___x_315_, 7);
v_infoState_323_ = lean_ctor_get(v___x_315_, 8);
v_snapshotTasks_324_ = lean_ctor_get(v___x_315_, 9);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_420_ == 0)
{
lean_object* v_unused_421_; 
v_unused_421_ = lean_ctor_get(v___x_315_, 5);
lean_dec(v_unused_421_);
v___x_326_ = v___x_315_;
v_isShared_327_ = v_isSharedCheck_420_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_snapshotTasks_324_);
lean_inc(v_infoState_323_);
lean_inc(v_messages_322_);
lean_inc(v_recordedDeps_321_);
lean_inc(v_traceState_320_);
lean_inc(v_auxDeclNGen_319_);
lean_inc(v_ngen_318_);
lean_inc(v_nextMacroScope_317_);
lean_inc(v_env_316_);
lean_dec(v___x_315_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_420_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
lean_inc(v_implName_270_);
v___x_328_ = l_Lean_Meta_addToCompletionBlackList(v_env_316_, v_implName_270_);
v___x_329_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 5, v___x_329_);
lean_ctor_set(v___x_326_, 0, v___x_328_);
v___x_331_ = v___x_326_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_nextMacroScope_317_);
lean_ctor_set(v_reuseFailAlloc_419_, 2, v_ngen_318_);
lean_ctor_set(v_reuseFailAlloc_419_, 3, v_auxDeclNGen_319_);
lean_ctor_set(v_reuseFailAlloc_419_, 4, v_traceState_320_);
lean_ctor_set(v_reuseFailAlloc_419_, 5, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_419_, 6, v_recordedDeps_321_);
lean_ctor_set(v_reuseFailAlloc_419_, 7, v_messages_322_);
lean_ctor_set(v_reuseFailAlloc_419_, 8, v_infoState_323_);
lean_ctor_set(v_reuseFailAlloc_419_, 9, v_snapshotTasks_324_);
v___x_331_ = v_reuseFailAlloc_419_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v_mctx_334_; lean_object* v_zetaDeltaFVarIds_335_; lean_object* v_postponed_336_; lean_object* v_diag_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_417_; 
v___x_332_ = lean_st_ref_put(v_a_267_, v___x_331_);
v___x_333_ = lean_st_ref_take(v_a_265_);
v_mctx_334_ = lean_ctor_get(v___x_333_, 0);
v_zetaDeltaFVarIds_335_ = lean_ctor_get(v___x_333_, 2);
v_postponed_336_ = lean_ctor_get(v___x_333_, 3);
v_diag_337_ = lean_ctor_get(v___x_333_, 4);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_417_ == 0)
{
lean_object* v_unused_418_; 
v_unused_418_ = lean_ctor_get(v___x_333_, 1);
lean_dec(v_unused_418_);
v___x_339_ = v___x_333_;
v_isShared_340_ = v_isSharedCheck_417_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_diag_337_);
lean_inc(v_postponed_336_);
lean_inc(v_zetaDeltaFVarIds_335_);
lean_inc(v_mctx_334_);
lean_dec(v___x_333_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_417_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_341_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 1, v___x_341_);
v___x_343_ = v___x_339_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_mctx_334_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_416_, 2, v_zetaDeltaFVarIds_335_);
lean_ctor_set(v_reuseFailAlloc_416_, 3, v_postponed_336_);
lean_ctor_set(v_reuseFailAlloc_416_, 4, v_diag_337_);
v___x_343_ = v_reuseFailAlloc_416_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v_env_346_; lean_object* v_nextMacroScope_347_; lean_object* v_ngen_348_; lean_object* v_auxDeclNGen_349_; lean_object* v_traceState_350_; lean_object* v_recordedDeps_351_; lean_object* v_messages_352_; lean_object* v_infoState_353_; lean_object* v_snapshotTasks_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_414_; 
v___x_344_ = lean_st_ref_put(v_a_265_, v___x_343_);
v___x_345_ = lean_st_ref_take(v_a_267_);
v_env_346_ = lean_ctor_get(v___x_345_, 0);
v_nextMacroScope_347_ = lean_ctor_get(v___x_345_, 1);
v_ngen_348_ = lean_ctor_get(v___x_345_, 2);
v_auxDeclNGen_349_ = lean_ctor_get(v___x_345_, 3);
v_traceState_350_ = lean_ctor_get(v___x_345_, 4);
v_recordedDeps_351_ = lean_ctor_get(v___x_345_, 6);
v_messages_352_ = lean_ctor_get(v___x_345_, 7);
v_infoState_353_ = lean_ctor_get(v___x_345_, 8);
v_snapshotTasks_354_ = lean_ctor_get(v___x_345_, 9);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; 
v_unused_415_ = lean_ctor_get(v___x_345_, 5);
lean_dec(v_unused_415_);
v___x_356_ = v___x_345_;
v_isShared_357_ = v_isSharedCheck_414_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_snapshotTasks_354_);
lean_inc(v_infoState_353_);
lean_inc(v_messages_352_);
lean_inc(v_recordedDeps_351_);
lean_inc(v_traceState_350_);
lean_inc(v_auxDeclNGen_349_);
lean_inc(v_ngen_348_);
lean_inc(v_nextMacroScope_347_);
lean_inc(v_env_346_);
lean_dec(v___x_345_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_414_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_358_; lean_object* v___x_360_; 
lean_inc(v_implName_270_);
v___x_358_ = l_Lean_addProtected(v_env_346_, v_implName_270_);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 5, v___x_329_);
lean_ctor_set(v___x_356_, 0, v___x_358_);
v___x_360_ = v___x_356_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_358_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_nextMacroScope_347_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v_ngen_348_);
lean_ctor_set(v_reuseFailAlloc_413_, 3, v_auxDeclNGen_349_);
lean_ctor_set(v_reuseFailAlloc_413_, 4, v_traceState_350_);
lean_ctor_set(v_reuseFailAlloc_413_, 5, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_413_, 6, v_recordedDeps_351_);
lean_ctor_set(v_reuseFailAlloc_413_, 7, v_messages_352_);
lean_ctor_set(v_reuseFailAlloc_413_, 8, v_infoState_353_);
lean_ctor_set(v_reuseFailAlloc_413_, 9, v_snapshotTasks_354_);
v___x_360_ = v_reuseFailAlloc_413_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v_mctx_363_; lean_object* v_zetaDeltaFVarIds_364_; lean_object* v_postponed_365_; lean_object* v_diag_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_411_; 
v___x_361_ = lean_st_ref_put(v_a_267_, v___x_360_);
v___x_362_ = lean_st_ref_take(v_a_265_);
v_mctx_363_ = lean_ctor_get(v___x_362_, 0);
v_zetaDeltaFVarIds_364_ = lean_ctor_get(v___x_362_, 2);
v_postponed_365_ = lean_ctor_get(v___x_362_, 3);
v_diag_366_ = lean_ctor_get(v___x_362_, 4);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; 
v_unused_412_ = lean_ctor_get(v___x_362_, 1);
lean_dec(v_unused_412_);
v___x_368_ = v___x_362_;
v_isShared_369_ = v_isSharedCheck_411_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_diag_366_);
lean_inc(v_postponed_365_);
lean_inc(v_zetaDeltaFVarIds_364_);
lean_inc(v_mctx_363_);
lean_dec(v___x_362_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_411_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v___x_341_);
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_mctx_363_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_zetaDeltaFVarIds_364_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v_postponed_365_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v_diag_366_);
v___x_371_ = v_reuseFailAlloc_410_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v_env_374_; uint8_t v___x_375_; 
v___x_372_ = lean_st_ref_put(v_a_265_, v___x_371_);
v___x_373_ = lean_st_ref_get(v_a_267_);
v_env_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc_ref(v_env_374_);
lean_dec(v___x_373_);
v___x_375_ = l_Lean_isMarkedMeta(v_env_374_, v_indName_261_);
if (v___x_375_ == 0)
{
v___y_282_ = v_a_264_;
v___y_283_ = v_a_265_;
v___y_284_ = v_a_266_;
v___y_285_ = v_a_267_;
goto v___jp_281_;
}
else
{
lean_object* v___x_376_; lean_object* v_env_377_; lean_object* v_nextMacroScope_378_; lean_object* v_ngen_379_; lean_object* v_auxDeclNGen_380_; lean_object* v_traceState_381_; lean_object* v_recordedDeps_382_; lean_object* v_messages_383_; lean_object* v_infoState_384_; lean_object* v_snapshotTasks_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_408_; 
v___x_376_ = lean_st_ref_take(v_a_267_);
v_env_377_ = lean_ctor_get(v___x_376_, 0);
v_nextMacroScope_378_ = lean_ctor_get(v___x_376_, 1);
v_ngen_379_ = lean_ctor_get(v___x_376_, 2);
v_auxDeclNGen_380_ = lean_ctor_get(v___x_376_, 3);
v_traceState_381_ = lean_ctor_get(v___x_376_, 4);
v_recordedDeps_382_ = lean_ctor_get(v___x_376_, 6);
v_messages_383_ = lean_ctor_get(v___x_376_, 7);
v_infoState_384_ = lean_ctor_get(v___x_376_, 8);
v_snapshotTasks_385_ = lean_ctor_get(v___x_376_, 9);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; 
v_unused_409_ = lean_ctor_get(v___x_376_, 5);
lean_dec(v_unused_409_);
v___x_387_ = v___x_376_;
v_isShared_388_ = v_isSharedCheck_408_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_snapshotTasks_385_);
lean_inc(v_infoState_384_);
lean_inc(v_messages_383_);
lean_inc(v_recordedDeps_382_);
lean_inc(v_traceState_381_);
lean_inc(v_auxDeclNGen_380_);
lean_inc(v_ngen_379_);
lean_inc(v_nextMacroScope_378_);
lean_inc(v_env_377_);
lean_dec(v___x_376_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_408_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_391_; 
lean_inc(v_implName_270_);
v___x_389_ = l_Lean_markMeta(v_env_377_, v_implName_270_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 5, v___x_329_);
lean_ctor_set(v___x_387_, 0, v___x_389_);
v___x_391_ = v___x_387_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_389_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_nextMacroScope_378_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_ngen_379_);
lean_ctor_set(v_reuseFailAlloc_407_, 3, v_auxDeclNGen_380_);
lean_ctor_set(v_reuseFailAlloc_407_, 4, v_traceState_381_);
lean_ctor_set(v_reuseFailAlloc_407_, 5, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_407_, 6, v_recordedDeps_382_);
lean_ctor_set(v_reuseFailAlloc_407_, 7, v_messages_383_);
lean_ctor_set(v_reuseFailAlloc_407_, 8, v_infoState_384_);
lean_ctor_set(v_reuseFailAlloc_407_, 9, v_snapshotTasks_385_);
v___x_391_ = v_reuseFailAlloc_407_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v_mctx_394_; lean_object* v_zetaDeltaFVarIds_395_; lean_object* v_postponed_396_; lean_object* v_diag_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_405_; 
v___x_392_ = lean_st_ref_put(v_a_267_, v___x_391_);
v___x_393_ = lean_st_ref_take(v_a_265_);
v_mctx_394_ = lean_ctor_get(v___x_393_, 0);
v_zetaDeltaFVarIds_395_ = lean_ctor_get(v___x_393_, 2);
v_postponed_396_ = lean_ctor_get(v___x_393_, 3);
v_diag_397_ = lean_ctor_get(v___x_393_, 4);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; 
v_unused_406_ = lean_ctor_get(v___x_393_, 1);
lean_dec(v_unused_406_);
v___x_399_ = v___x_393_;
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_diag_397_);
lean_inc(v_postponed_396_);
lean_inc(v_zetaDeltaFVarIds_395_);
lean_inc(v_mctx_394_);
lean_dec(v___x_393_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 1, v___x_341_);
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_mctx_394_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v___x_341_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v_zetaDeltaFVarIds_395_);
lean_ctor_set(v_reuseFailAlloc_404_, 3, v_postponed_396_);
lean_ctor_set(v_reuseFailAlloc_404_, 4, v_diag_397_);
v___x_402_ = v_reuseFailAlloc_404_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; 
v___x_403_ = lean_st_ref_put(v_a_265_, v___x_402_);
v___y_282_ = v_a_264_;
v___y_283_ = v_a_265_;
v___y_284_ = v_a_266_;
v___y_285_ = v_a_267_;
goto v___jp_281_;
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
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_dec_ref_known(v___x_280_, 1);
lean_dec(v_implName_270_);
lean_dec(v_indName_261_);
v_a_422_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_314_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_314_);
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
v___jp_281_:
{
uint8_t v___x_286_; lean_object* v___x_287_; 
v___x_286_ = 4;
lean_inc(v_implName_270_);
v___x_287_ = l_Lean_Meta_setInlineAttribute(v_implName_270_, v___x_286_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
if (lean_obj_tag(v___x_287_) == 0)
{
uint8_t v___x_288_; lean_object* v___x_289_; 
lean_dec_ref_known(v___x_287_, 1);
v___x_288_ = 1;
v___x_289_ = l_Lean_compileDecl(v___x_280_, v___x_288_, v___y_284_, v___y_285_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; 
v_unused_297_ = lean_ctor_get(v___x_289_, 0);
lean_dec(v_unused_297_);
v___x_291_ = v___x_289_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_dec(v___x_289_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v_implName_270_);
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_implName_270_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec(v_implName_270_);
v_a_298_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_289_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_289_);
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
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_313_; 
lean_dec_ref_known(v___x_280_, 1);
lean_dec(v_implName_270_);
v_a_306_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_313_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_313_ == 0)
{
v___x_308_ = v___x_287_;
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_287_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_313_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_311_; 
if (v_isShared_309_ == 0)
{
v___x_311_ = v___x_308_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v_a_306_);
v___x_311_ = v_reuseFailAlloc_312_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
return v___x_311_;
}
}
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
lean_dec(v_implName_270_);
lean_dec_ref(v_declType_263_);
lean_dec(v_levelParams_262_);
lean_dec(v_indName_261_);
v_a_430_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_272_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_272_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_0interp(lean_interpreter_value* stack)
{
lean_object* v_indName_261_ = stack[0].m_obj;
lean_object* v_levelParams_262_ = stack[1].m_obj;
lean_object* v_declType_263_ = stack[2].m_obj;
lean_object* v_a_264_ = stack[3].m_obj;
lean_object* v_a_265_ = stack[4].m_obj;
lean_object* v_a_266_ = stack[5].m_obj;
lean_object* v_a_267_ = stack[6].m_obj;
lean_object* v_res_438_;
v_res_438_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl(v_indName_261_, v_levelParams_262_, v_declType_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_);
stack->m_obj
 = v_res_438_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___boxed(lean_object* v_indName_439_, lean_object* v_levelParams_440_, lean_object* v_declType_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl(v_indName_439_, v_levelParams_440_, v_declType_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
return v_res_447_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(lean_object* v_opts_448_, lean_object* v_opt_449_){
_start:
{
lean_object* v_name_450_; lean_object* v_defValue_451_; lean_object* v_map_452_; lean_object* v___x_453_; 
v_name_450_ = lean_ctor_get(v_opt_449_, 0);
v_defValue_451_ = lean_ctor_get(v_opt_449_, 1);
v_map_452_ = lean_ctor_get(v_opts_448_, 0);
v___x_453_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_452_, v_name_450_);
if (lean_obj_tag(v___x_453_) == 0)
{
uint8_t v___x_454_; 
v___x_454_ = lean_unbox(v_defValue_451_);
return v___x_454_;
}
else
{
lean_object* v_val_455_; 
v_val_455_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_val_455_);
lean_dec_ref_known(v___x_453_, 1);
if (lean_obj_tag(v_val_455_) == 1)
{
uint8_t v_v_456_; 
v_v_456_ = lean_ctor_get_uint8(v_val_455_, 0);
lean_dec_ref_known(v_val_455_, 0);
return v_v_456_;
}
else
{
uint8_t v___x_457_; 
lean_dec(v_val_455_);
v___x_457_ = lean_unbox(v_defValue_451_);
return v___x_457_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_448_ = stack[0].m_obj;
lean_object* v_opt_449_ = stack[1].m_obj;
uint8_t v_res_458_;
v_res_458_ = l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(v_opts_448_, v_opt_449_);
stack->m_num = v_res_458_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0___boxed(lean_object* v_opts_459_, lean_object* v_opt_460_){
_start:
{
uint8_t v_res_461_; lean_object* v_r_462_; 
v_res_461_ = l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(v_opts_459_, v_opt_460_);
lean_dec_ref(v_opt_460_);
lean_dec_ref(v_opts_459_);
v_r_462_ = lean_box(v_res_461_);
return v_r_462_;
}
}
lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(lean_object* v_constName_463_, uint8_t v_skipRealize_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___x_467_; lean_object* v_env_468_; uint8_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_467_ = lean_st_ref_get(v___y_465_);
v_env_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc_ref(v_env_468_);
lean_dec(v___x_467_);
v___x_469_ = l_Lean_Environment_contains(v_env_468_, v_constName_463_, v_skipRealize_464_);
v___x_470_ = lean_box(v___x_469_);
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT void l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_463_ = stack[0].m_obj;
uint8_t v_skipRealize_464_ = stack[1].m_num;
lean_object* v___y_465_ = stack[2].m_obj;
lean_object* v_res_472_;
v_res_472_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v_constName_463_, v_skipRealize_464_, v___y_465_);
stack->m_obj
 = v_res_472_;
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg___boxed(lean_object* v_constName_473_, lean_object* v_skipRealize_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
uint8_t v_skipRealize_boxed_477_; lean_object* v_res_478_; 
v_skipRealize_boxed_477_ = lean_unbox(v_skipRealize_474_);
v_res_478_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v_constName_473_, v_skipRealize_boxed_477_, v___y_475_);
lean_dec(v___y_475_);
return v_res_478_;
}
}
lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1(lean_object* v_constName_479_, uint8_t v_skipRealize_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v_constName_479_, v_skipRealize_480_, v___y_484_);
return v___x_486_;
}
}
LEAN_EXPORT void l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_479_ = stack[0].m_obj;
uint8_t v_skipRealize_480_ = stack[1].m_num;
lean_object* v___y_481_ = stack[2].m_obj;
lean_object* v___y_482_ = stack[3].m_obj;
lean_object* v___y_483_ = stack[4].m_obj;
lean_object* v___y_484_ = stack[5].m_obj;
lean_object* v_res_487_;
v_res_487_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1(v_constName_479_, v_skipRealize_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
stack->m_obj
 = v_res_487_;
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___boxed(lean_object* v_constName_488_, lean_object* v_skipRealize_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
uint8_t v_skipRealize_boxed_495_; lean_object* v_res_496_; 
v_skipRealize_boxed_495_ = lean_unbox(v_skipRealize_489_);
v_res_496_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1(v_constName_488_, v_skipRealize_boxed_495_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
return v_res_496_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(lean_object* v_type_497_, lean_object* v_maxFVars_x3f_498_, lean_object* v_k_499_, uint8_t v_cleanupAnnotations_500_, uint8_t v_whnfType_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v___f_507_; lean_object* v___x_508_; 
v___f_507_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_507_, 0, v_k_499_);
v___x_508_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_497_, v_maxFVars_x3f_498_, v___f_507_, v_cleanupAnnotations_500_, v_whnfType_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
v_a_517_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_508_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_508_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
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
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_497_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_498_ = stack[1].m_obj;
lean_object* v_k_499_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_500_ = stack[3].m_num;
uint8_t v_whnfType_501_ = stack[4].m_num;
lean_object* v___y_502_ = stack[5].m_obj;
lean_object* v___y_503_ = stack[6].m_obj;
lean_object* v___y_504_ = stack[7].m_obj;
lean_object* v___y_505_ = stack[8].m_obj;
lean_object* v_res_525_;
v_res_525_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_497_, v_maxFVars_x3f_498_, v_k_499_, v_cleanupAnnotations_500_, v_whnfType_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
stack->m_obj
 = v_res_525_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___boxed(lean_object* v_type_526_, lean_object* v_maxFVars_x3f_527_, lean_object* v_k_528_, lean_object* v_cleanupAnnotations_529_, lean_object* v_whnfType_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_536_; uint8_t v_whnfType_boxed_537_; lean_object* v_res_538_; 
v_cleanupAnnotations_boxed_536_ = lean_unbox(v_cleanupAnnotations_529_);
v_whnfType_boxed_537_ = lean_unbox(v_whnfType_530_);
v_res_538_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_526_, v_maxFVars_x3f_527_, v_k_528_, v_cleanupAnnotations_boxed_536_, v_whnfType_boxed_537_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
return v_res_538_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5(lean_object* v_00_u03b1_539_, lean_object* v_type_540_, lean_object* v_maxFVars_x3f_541_, lean_object* v_k_542_, uint8_t v_cleanupAnnotations_543_, uint8_t v_whnfType_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_540_, v_maxFVars_x3f_541_, v_k_542_, v_cleanupAnnotations_543_, v_whnfType_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
return v___x_550_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_540_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_541_ = stack[2].m_obj;
lean_object* v_k_542_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_543_ = stack[4].m_num;
uint8_t v_whnfType_544_ = stack[5].m_num;
lean_object* v___y_545_ = stack[6].m_obj;
lean_object* v___y_546_ = stack[7].m_obj;
lean_object* v___y_547_ = stack[8].m_obj;
lean_object* v___y_548_ = stack[9].m_obj;
lean_object* v_res_551_;
v_res_551_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5(lean_box(0), v_type_540_, v_maxFVars_x3f_541_, v_k_542_, v_cleanupAnnotations_543_, v_whnfType_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
stack->m_obj
 = v_res_551_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___boxed(lean_object* v_00_u03b1_552_, lean_object* v_type_553_, lean_object* v_maxFVars_x3f_554_, lean_object* v_k_555_, lean_object* v_cleanupAnnotations_556_, lean_object* v_whnfType_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_563_; uint8_t v_whnfType_boxed_564_; lean_object* v_res_565_; 
v_cleanupAnnotations_boxed_563_ = lean_unbox(v_cleanupAnnotations_556_);
v_whnfType_boxed_564_ = lean_unbox(v_whnfType_557_);
v_res_565_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5(v_00_u03b1_552_, v_type_553_, v_maxFVars_x3f_554_, v_k_555_, v_cleanupAnnotations_boxed_563_, v_whnfType_boxed_564_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
return v_res_565_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(lean_object* v_name_566_, lean_object* v_levelParams_567_, lean_object* v_type_568_, lean_object* v_value_569_, lean_object* v_hints_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___x_573_; uint8_t v___y_575_; uint8_t v___y_582_; lean_object* v_env_585_; uint8_t v___x_586_; 
v___x_573_ = lean_st_ref_get(v___y_571_);
v_env_585_ = lean_ctor_get(v___x_573_, 0);
lean_inc_ref_n(v_env_585_, 2);
lean_dec(v___x_573_);
v___x_586_ = l_Lean_Environment_hasUnsafe(v_env_585_, v_type_568_);
if (v___x_586_ == 0)
{
uint8_t v___x_587_; 
v___x_587_ = l_Lean_Environment_hasUnsafe(v_env_585_, v_value_569_);
v___y_582_ = v___x_587_;
goto v___jp_581_;
}
else
{
lean_dec_ref(v_env_585_);
v___y_582_ = v___x_586_;
goto v___jp_581_;
}
v___jp_574_:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
lean_inc(v_name_566_);
v___x_576_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_576_, 0, v_name_566_);
lean_ctor_set(v___x_576_, 1, v_levelParams_567_);
lean_ctor_set(v___x_576_, 2, v_type_568_);
v___x_577_ = lean_box(0);
v___x_578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_578_, 0, v_name_566_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_579_, 0, v___x_576_);
lean_ctor_set(v___x_579_, 1, v_value_569_);
lean_ctor_set(v___x_579_, 2, v_hints_570_);
lean_ctor_set(v___x_579_, 3, v___x_578_);
lean_ctor_set_uint8(v___x_579_, sizeof(void*)*4, v___y_575_);
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
return v___x_580_;
}
v___jp_581_:
{
if (v___y_582_ == 0)
{
uint8_t v___x_583_; 
v___x_583_ = 1;
v___y_575_ = v___x_583_;
goto v___jp_574_;
}
else
{
uint8_t v___x_584_; 
v___x_584_ = 0;
v___y_575_ = v___x_584_;
goto v___jp_574_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_566_ = stack[0].m_obj;
lean_object* v_levelParams_567_ = stack[1].m_obj;
lean_object* v_type_568_ = stack[2].m_obj;
lean_object* v_value_569_ = stack[3].m_obj;
lean_object* v_hints_570_ = stack[4].m_obj;
lean_object* v___y_571_ = stack[5].m_obj;
lean_object* v_res_588_;
v_res_588_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v_name_566_, v_levelParams_567_, v_type_568_, v_value_569_, v_hints_570_, v___y_571_);
stack->m_obj
 = v_res_588_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg___boxed(lean_object* v_name_589_, lean_object* v_levelParams_590_, lean_object* v_type_591_, lean_object* v_value_592_, lean_object* v_hints_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v_name_589_, v_levelParams_590_, v_type_591_, v_value_592_, v_hints_593_, v___y_594_);
lean_dec(v___y_594_);
return v_res_596_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8(lean_object* v_name_597_, lean_object* v_levelParams_598_, lean_object* v_type_599_, lean_object* v_value_600_, lean_object* v_hints_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v_name_597_, v_levelParams_598_, v_type_599_, v_value_600_, v_hints_601_, v___y_605_);
return v___x_607_;
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_597_ = stack[0].m_obj;
lean_object* v_levelParams_598_ = stack[1].m_obj;
lean_object* v_type_599_ = stack[2].m_obj;
lean_object* v_value_600_ = stack[3].m_obj;
lean_object* v_hints_601_ = stack[4].m_obj;
lean_object* v___y_602_ = stack[5].m_obj;
lean_object* v___y_603_ = stack[6].m_obj;
lean_object* v___y_604_ = stack[7].m_obj;
lean_object* v___y_605_ = stack[8].m_obj;
lean_object* v_res_608_;
v_res_608_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8(v_name_597_, v_levelParams_598_, v_type_599_, v_value_600_, v_hints_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
stack->m_obj
 = v_res_608_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___boxed(lean_object* v_name_609_, lean_object* v_levelParams_610_, lean_object* v_type_611_, lean_object* v_value_612_, lean_object* v_hints_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8(v_name_609_, v_levelParams_610_, v_type_611_, v_value_612_, v_hints_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
return v_res_619_;
}
}
lean_object* l_panic___at___00Lean_mkCtorIdx_spec__11(lean_object* v_msg_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v___f_627_; lean_object* v___x_12996__overap_628_; lean_object* v___x_629_; 
v___f_627_ = ((lean_object*)(l_panic___at___00Lean_mkCtorIdx_spec__11___closed__0));
v___x_12996__overap_628_ = lean_panic_fn_borrowed(v___f_627_, v_msg_621_);
lean_inc(v___y_625_);
lean_inc_ref(v___y_624_);
lean_inc(v___y_623_);
lean_inc_ref(v___y_622_);
v___x_629_ = lean_apply_5(v___x_12996__overap_628_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, lean_box(0));
return v___x_629_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_mkCtorIdx_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_621_ = stack[0].m_obj;
lean_object* v___y_622_ = stack[1].m_obj;
lean_object* v___y_623_ = stack[2].m_obj;
lean_object* v___y_624_ = stack[3].m_obj;
lean_object* v___y_625_ = stack[4].m_obj;
lean_object* v_res_630_;
v_res_630_ = l_panic___at___00Lean_mkCtorIdx_spec__11(v_msg_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
stack->m_obj
 = v_res_630_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCtorIdx_spec__11___boxed(lean_object* v_msg_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_panic___at___00Lean_mkCtorIdx_spec__11(v_msg_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
return v_res_637_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0(lean_object* v___y_638_, uint8_t v_isExporting_639_, lean_object* v___x_640_, lean_object* v___y_641_, lean_object* v___x_642_, lean_object* v_a_x3f_643_){
_start:
{
lean_object* v___x_645_; lean_object* v_env_646_; lean_object* v_nextMacroScope_647_; lean_object* v_ngen_648_; lean_object* v_auxDeclNGen_649_; lean_object* v_traceState_650_; lean_object* v_recordedDeps_651_; lean_object* v_messages_652_; lean_object* v_infoState_653_; lean_object* v_snapshotTasks_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_679_; 
v___x_645_ = lean_st_ref_take(v___y_638_);
v_env_646_ = lean_ctor_get(v___x_645_, 0);
v_nextMacroScope_647_ = lean_ctor_get(v___x_645_, 1);
v_ngen_648_ = lean_ctor_get(v___x_645_, 2);
v_auxDeclNGen_649_ = lean_ctor_get(v___x_645_, 3);
v_traceState_650_ = lean_ctor_get(v___x_645_, 4);
v_recordedDeps_651_ = lean_ctor_get(v___x_645_, 6);
v_messages_652_ = lean_ctor_get(v___x_645_, 7);
v_infoState_653_ = lean_ctor_get(v___x_645_, 8);
v_snapshotTasks_654_ = lean_ctor_get(v___x_645_, 9);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_679_ == 0)
{
lean_object* v_unused_680_; 
v_unused_680_ = lean_ctor_get(v___x_645_, 5);
lean_dec(v_unused_680_);
v___x_656_ = v___x_645_;
v_isShared_657_ = v_isSharedCheck_679_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_snapshotTasks_654_);
lean_inc(v_infoState_653_);
lean_inc(v_messages_652_);
lean_inc(v_recordedDeps_651_);
lean_inc(v_traceState_650_);
lean_inc(v_auxDeclNGen_649_);
lean_inc(v_ngen_648_);
lean_inc(v_nextMacroScope_647_);
lean_inc(v_env_646_);
lean_dec(v___x_645_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_679_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_658_ = l_Lean_Environment_setExporting(v_env_646_, v_isExporting_639_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 5, v___x_640_);
lean_ctor_set(v___x_656_, 0, v___x_658_);
v___x_660_ = v___x_656_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_nextMacroScope_647_);
lean_ctor_set(v_reuseFailAlloc_678_, 2, v_ngen_648_);
lean_ctor_set(v_reuseFailAlloc_678_, 3, v_auxDeclNGen_649_);
lean_ctor_set(v_reuseFailAlloc_678_, 4, v_traceState_650_);
lean_ctor_set(v_reuseFailAlloc_678_, 5, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_678_, 6, v_recordedDeps_651_);
lean_ctor_set(v_reuseFailAlloc_678_, 7, v_messages_652_);
lean_ctor_set(v_reuseFailAlloc_678_, 8, v_infoState_653_);
lean_ctor_set(v_reuseFailAlloc_678_, 9, v_snapshotTasks_654_);
v___x_660_ = v_reuseFailAlloc_678_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v_mctx_663_; lean_object* v_zetaDeltaFVarIds_664_; lean_object* v_postponed_665_; lean_object* v_diag_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_676_; 
v___x_661_ = lean_st_ref_put(v___y_638_, v___x_660_);
v___x_662_ = lean_st_ref_take(v___y_641_);
v_mctx_663_ = lean_ctor_get(v___x_662_, 0);
v_zetaDeltaFVarIds_664_ = lean_ctor_get(v___x_662_, 2);
v_postponed_665_ = lean_ctor_get(v___x_662_, 3);
v_diag_666_ = lean_ctor_get(v___x_662_, 4);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; 
v_unused_677_ = lean_ctor_get(v___x_662_, 1);
lean_dec(v_unused_677_);
v___x_668_ = v___x_662_;
v_isShared_669_ = v_isSharedCheck_676_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_diag_666_);
lean_inc(v_postponed_665_);
lean_inc(v_zetaDeltaFVarIds_664_);
lean_inc(v_mctx_663_);
lean_dec(v___x_662_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_676_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_670_ = lean_box(0);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 1, v___x_642_);
v___x_672_ = v___x_668_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_mctx_663_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_675_, 2, v_zetaDeltaFVarIds_664_);
lean_ctor_set(v_reuseFailAlloc_675_, 3, v_postponed_665_);
lean_ctor_set(v_reuseFailAlloc_675_, 4, v_diag_666_);
v___x_672_ = v_reuseFailAlloc_675_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_st_ref_put(v___y_641_, v___x_672_);
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_670_);
return v___x_674_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_638_ = stack[0].m_obj;
uint8_t v_isExporting_639_ = stack[1].m_num;
lean_object* v___x_640_ = stack[2].m_obj;
lean_object* v___y_641_ = stack[3].m_obj;
lean_object* v___x_642_ = stack[4].m_obj;
lean_object* v_a_x3f_643_ = stack[5].m_obj;
lean_object* v_res_681_;
v_res_681_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0(v___y_638_, v_isExporting_639_, v___x_640_, v___y_641_, v___x_642_, v_a_x3f_643_);
stack->m_obj
 = v_res_681_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0___boxed(lean_object* v___y_682_, lean_object* v_isExporting_683_, lean_object* v___x_684_, lean_object* v___y_685_, lean_object* v___x_686_, lean_object* v_a_x3f_687_, lean_object* v___y_688_){
_start:
{
uint8_t v_isExporting_boxed_689_; lean_object* v_res_690_; 
v_isExporting_boxed_689_ = lean_unbox(v_isExporting_683_);
v_res_690_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0(v___y_682_, v_isExporting_boxed_689_, v___x_684_, v___y_685_, v___x_686_, v_a_x3f_687_);
lean_dec(v_a_x3f_687_);
lean_dec(v___y_685_);
lean_dec(v___y_682_);
return v_res_690_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(lean_object* v_x_691_, uint8_t v_isExporting_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v___x_698_; lean_object* v_env_699_; lean_object* v___x_700_; uint8_t v_isModule_701_; 
v___x_698_ = lean_st_ref_get(v___y_696_);
v_env_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc_ref(v_env_699_);
lean_dec(v___x_698_);
v___x_700_ = l_Lean_Environment_header(v_env_699_);
v_isModule_701_ = lean_ctor_get_uint8(v___x_700_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_700_);
if (v_isModule_701_ == 0)
{
lean_object* v___x_702_; 
lean_dec_ref(v_env_699_);
lean_inc(v___y_696_);
lean_inc_ref(v___y_695_);
lean_inc(v___y_694_);
lean_inc_ref(v___y_693_);
v___x_702_ = lean_apply_5(v_x_691_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, lean_box(0));
return v___x_702_;
}
else
{
uint8_t v_isExporting_703_; 
v_isExporting_703_ = lean_ctor_get_uint8(v_env_699_, sizeof(void*)*13);
lean_dec_ref(v_env_699_);
if (v_isExporting_692_ == 0)
{
if (v_isExporting_703_ == 0)
{
lean_object* v___x_770_; 
lean_inc(v___y_696_);
lean_inc_ref(v___y_695_);
lean_inc(v___y_694_);
lean_inc_ref(v___y_693_);
v___x_770_ = lean_apply_5(v_x_691_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, lean_box(0));
return v___x_770_;
}
else
{
goto v___jp_704_;
}
}
else
{
if (v_isExporting_703_ == 0)
{
goto v___jp_704_;
}
else
{
lean_object* v___x_771_; 
lean_inc(v___y_696_);
lean_inc_ref(v___y_695_);
lean_inc(v___y_694_);
lean_inc_ref(v___y_693_);
v___x_771_ = lean_apply_5(v_x_691_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, lean_box(0));
return v___x_771_;
}
}
v___jp_704_:
{
lean_object* v___x_705_; lean_object* v_env_706_; lean_object* v_nextMacroScope_707_; lean_object* v_ngen_708_; lean_object* v_auxDeclNGen_709_; lean_object* v_traceState_710_; lean_object* v_recordedDeps_711_; lean_object* v_messages_712_; lean_object* v_infoState_713_; lean_object* v_snapshotTasks_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_768_; 
v___x_705_ = lean_st_ref_take(v___y_696_);
v_env_706_ = lean_ctor_get(v___x_705_, 0);
v_nextMacroScope_707_ = lean_ctor_get(v___x_705_, 1);
v_ngen_708_ = lean_ctor_get(v___x_705_, 2);
v_auxDeclNGen_709_ = lean_ctor_get(v___x_705_, 3);
v_traceState_710_ = lean_ctor_get(v___x_705_, 4);
v_recordedDeps_711_ = lean_ctor_get(v___x_705_, 6);
v_messages_712_ = lean_ctor_get(v___x_705_, 7);
v_infoState_713_ = lean_ctor_get(v___x_705_, 8);
v_snapshotTasks_714_ = lean_ctor_get(v___x_705_, 9);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; 
v_unused_769_ = lean_ctor_get(v___x_705_, 5);
lean_dec(v_unused_769_);
v___x_716_ = v___x_705_;
v_isShared_717_ = v_isSharedCheck_768_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_snapshotTasks_714_);
lean_inc(v_infoState_713_);
lean_inc(v_messages_712_);
lean_inc(v_recordedDeps_711_);
lean_inc(v_traceState_710_);
lean_inc(v_auxDeclNGen_709_);
lean_inc(v_ngen_708_);
lean_inc(v_nextMacroScope_707_);
lean_inc(v_env_706_);
lean_dec(v___x_705_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_768_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_718_ = l_Lean_Environment_setExporting(v_env_706_, v_isExporting_692_);
v___x_719_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 5, v___x_719_);
lean_ctor_set(v___x_716_, 0, v___x_718_);
v___x_721_ = v___x_716_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_nextMacroScope_707_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v_ngen_708_);
lean_ctor_set(v_reuseFailAlloc_767_, 3, v_auxDeclNGen_709_);
lean_ctor_set(v_reuseFailAlloc_767_, 4, v_traceState_710_);
lean_ctor_set(v_reuseFailAlloc_767_, 5, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_767_, 6, v_recordedDeps_711_);
lean_ctor_set(v_reuseFailAlloc_767_, 7, v_messages_712_);
lean_ctor_set(v_reuseFailAlloc_767_, 8, v_infoState_713_);
lean_ctor_set(v_reuseFailAlloc_767_, 9, v_snapshotTasks_714_);
v___x_721_ = v_reuseFailAlloc_767_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v_mctx_724_; lean_object* v_zetaDeltaFVarIds_725_; lean_object* v_postponed_726_; lean_object* v_diag_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_765_; 
v___x_722_ = lean_st_ref_put(v___y_696_, v___x_721_);
v___x_723_ = lean_st_ref_take(v___y_694_);
v_mctx_724_ = lean_ctor_get(v___x_723_, 0);
v_zetaDeltaFVarIds_725_ = lean_ctor_get(v___x_723_, 2);
v_postponed_726_ = lean_ctor_get(v___x_723_, 3);
v_diag_727_ = lean_ctor_get(v___x_723_, 4);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v___x_723_, 1);
lean_dec(v_unused_766_);
v___x_729_ = v___x_723_;
v_isShared_730_ = v_isSharedCheck_765_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_diag_727_);
lean_inc(v_postponed_726_);
lean_inc(v_zetaDeltaFVarIds_725_);
lean_inc(v_mctx_724_);
lean_dec(v___x_723_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_765_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_731_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v___x_731_);
v___x_733_ = v___x_729_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_mctx_724_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v_zetaDeltaFVarIds_725_);
lean_ctor_set(v_reuseFailAlloc_764_, 3, v_postponed_726_);
lean_ctor_set(v_reuseFailAlloc_764_, 4, v_diag_727_);
v___x_733_ = v_reuseFailAlloc_764_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; lean_object* v_r_735_; 
v___x_734_ = lean_st_ref_put(v___y_694_, v___x_733_);
lean_inc(v___y_696_);
lean_inc_ref(v___y_695_);
lean_inc(v___y_694_);
lean_inc_ref(v___y_693_);
v_r_735_ = lean_apply_5(v_x_691_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, lean_box(0));
if (lean_obj_tag(v_r_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_752_; 
v_a_736_ = lean_ctor_get(v_r_735_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v_r_735_);
if (v_isSharedCheck_752_ == 0)
{
v___x_738_ = v_r_735_;
v_isShared_739_ = v_isSharedCheck_752_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v_r_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_752_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
lean_inc(v_a_736_);
if (v_isShared_739_ == 0)
{
lean_ctor_set_tag(v___x_738_, 1);
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_751_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
v___x_742_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0(v___y_696_, v_isExporting_703_, v___x_719_, v___y_694_, v___x_731_, v___x_741_);
lean_dec_ref(v___x_741_);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; 
v_unused_750_ = lean_ctor_get(v___x_742_, 0);
lean_dec(v_unused_750_);
v___x_744_ = v___x_742_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_dec(v___x_742_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v_a_736_);
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_736_);
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
}
else
{
lean_object* v_a_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
v_a_753_ = lean_ctor_get(v_r_735_, 0);
lean_inc(v_a_753_);
lean_dec_ref_known(v_r_735_, 1);
v___x_754_ = lean_box(0);
v___x_755_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___lam__0(v___y_696_, v_isExporting_703_, v___x_719_, v___y_694_, v___x_731_, v___x_754_);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; 
v_unused_763_ = lean_ctor_get(v___x_755_, 0);
lean_dec(v_unused_763_);
v___x_757_ = v___x_755_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_dec(v___x_755_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set_tag(v___x_757_, 1);
lean_ctor_set(v___x_757_, 0, v_a_753_);
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_753_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
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
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_691_ = stack[0].m_obj;
uint8_t v_isExporting_692_ = stack[1].m_num;
lean_object* v___y_693_ = stack[2].m_obj;
lean_object* v___y_694_ = stack[3].m_obj;
lean_object* v___y_695_ = stack[4].m_obj;
lean_object* v___y_696_ = stack[5].m_obj;
lean_object* v_res_772_;
v_res_772_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(v_x_691_, v_isExporting_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
stack->m_obj
 = v_res_772_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg___boxed(lean_object* v_x_773_, lean_object* v_isExporting_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
uint8_t v_isExporting_boxed_780_; lean_object* v_res_781_; 
v_isExporting_boxed_780_ = lean_unbox(v_isExporting_774_);
v_res_781_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(v_x_773_, v_isExporting_boxed_780_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
return v_res_781_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12(lean_object* v_00_u03b1_782_, lean_object* v_x_783_, uint8_t v_isExporting_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(v_x_783_, v_isExporting_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
return v___x_790_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_783_ = stack[1].m_obj;
uint8_t v_isExporting_784_ = stack[2].m_num;
lean_object* v___y_785_ = stack[3].m_obj;
lean_object* v___y_786_ = stack[4].m_obj;
lean_object* v___y_787_ = stack[5].m_obj;
lean_object* v___y_788_ = stack[6].m_obj;
lean_object* v_res_791_;
v_res_791_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12(lean_box(0), v_x_783_, v_isExporting_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
stack->m_obj
 = v_res_791_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___boxed(lean_object* v_00_u03b1_792_, lean_object* v_x_793_, lean_object* v_isExporting_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
uint8_t v_isExporting_boxed_800_; lean_object* v_res_801_; 
v_isExporting_boxed_800_ = lean_unbox(v_isExporting_794_);
v_res_801_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12(v_00_u03b1_792_, v_x_793_, v_isExporting_boxed_800_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
return v_res_801_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(lean_object* v_cidx_802_, uint8_t v___x_803_, uint8_t v___x_804_, uint8_t v___x_805_, lean_object* v_ys_806_, lean_object* v_x_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = l_Lean_mkRawNatLit(v_cidx_802_);
v___x_814_ = l_Lean_Meta_mkLambdaFVars(v_ys_806_, v___x_813_, v___x_803_, v___x_804_, v___x_803_, v___x_804_, v___x_805_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
return v___x_814_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cidx_802_ = stack[0].m_obj;
uint8_t v___x_803_ = stack[1].m_num;
uint8_t v___x_804_ = stack[2].m_num;
uint8_t v___x_805_ = stack[3].m_num;
lean_object* v_ys_806_ = stack[4].m_obj;
lean_object* v_x_807_ = stack[5].m_obj;
lean_object* v___y_808_ = stack[6].m_obj;
lean_object* v___y_809_ = stack[7].m_obj;
lean_object* v___y_810_ = stack[8].m_obj;
lean_object* v___y_811_ = stack[9].m_obj;
lean_object* v_res_815_;
v_res_815_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(v_cidx_802_, v___x_803_, v___x_804_, v___x_805_, v_ys_806_, v_x_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
stack->m_obj
 = v_res_815_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed(lean_object* v_cidx_816_, lean_object* v___x_817_, lean_object* v___x_818_, lean_object* v___x_819_, lean_object* v_ys_820_, lean_object* v_x_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
uint8_t v___x_20521__boxed_827_; uint8_t v___x_20522__boxed_828_; uint8_t v___x_20523__boxed_829_; lean_object* v_res_830_; 
v___x_20521__boxed_827_ = lean_unbox(v___x_817_);
v___x_20522__boxed_828_ = lean_unbox(v___x_818_);
v___x_20523__boxed_829_ = lean_unbox(v___x_819_);
v_res_830_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(v_cidx_816_, v___x_20521__boxed_827_, v___x_20522__boxed_828_, v___x_20523__boxed_829_, v_ys_820_, v_x_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec_ref(v_x_821_);
lean_dec_ref(v_ys_820_);
return v_res_830_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(lean_object* v_msgData_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___x_837_; lean_object* v_env_838_; uint8_t v___x_839_; lean_object* v_env_840_; lean_object* v___x_841_; lean_object* v_toCold_842_; lean_object* v_mctx_843_; lean_object* v_lctx_844_; lean_object* v_options_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_837_ = lean_st_ref_get(v___y_835_);
v_env_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc_ref(v_env_838_);
lean_dec(v___x_837_);
v___x_839_ = 0;
v_env_840_ = l_Lean_Environment_setRecordingDeps(v_env_838_, v___x_839_);
v___x_841_ = lean_st_ref_get(v___y_833_);
v_toCold_842_ = lean_ctor_get(v___y_834_, 0);
v_mctx_843_ = lean_ctor_get(v___x_841_, 0);
lean_inc_ref(v_mctx_843_);
lean_dec(v___x_841_);
v_lctx_844_ = lean_ctor_get(v___y_832_, 2);
v_options_845_ = lean_ctor_get(v_toCold_842_, 2);
lean_inc_ref(v_options_845_);
lean_inc_ref(v_lctx_844_);
v___x_846_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_846_, 0, v_env_840_);
lean_ctor_set(v___x_846_, 1, v_mctx_843_);
lean_ctor_set(v___x_846_, 2, v_lctx_844_);
lean_ctor_set(v___x_846_, 3, v_options_845_);
v___x_847_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v_msgData_831_);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_831_ = stack[0].m_obj;
lean_object* v___y_832_ = stack[1].m_obj;
lean_object* v___y_833_ = stack[2].m_obj;
lean_object* v___y_834_ = stack[3].m_obj;
lean_object* v___y_835_ = stack[4].m_obj;
lean_object* v_res_849_;
v_res_849_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(v_msgData_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
stack->m_obj
 = v_res_849_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11___boxed(lean_object* v_msgData_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(v_msgData_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
return v_res_856_;
}
}
lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(lean_object* v_msg_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_ref_863_; lean_object* v___x_864_; lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_873_; 
v_ref_863_ = lean_ctor_get(v___y_860_, 2);
v___x_864_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(v_msg_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_873_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_871_; 
lean_inc(v_ref_863_);
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v_ref_863_);
lean_ctor_set(v___x_869_, 1, v_a_865_);
if (v_isShared_868_ == 0)
{
lean_ctor_set_tag(v___x_867_, 1);
lean_ctor_set(v___x_867_, 0, v___x_869_);
v___x_871_ = v___x_867_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
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
LEAN_EXPORT void l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_857_ = stack[0].m_obj;
lean_object* v___y_858_ = stack[1].m_obj;
lean_object* v___y_859_ = stack[2].m_obj;
lean_object* v___y_860_ = stack[3].m_obj;
lean_object* v___y_861_ = stack[4].m_obj;
lean_object* v_res_874_;
v_res_874_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
stack->m_obj
 = v_res_874_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg___boxed(lean_object* v_msg_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
return v_res_881_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0(void){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_instMonadEIO___redArg();
return v___x_882_;
}
}
lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(lean_object* v_msg_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v_toApplicative_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_956_; 
v___x_893_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0);
v___x_894_ = l_StateRefT_x27_instMonad___redArg(v___x_893_);
v_toApplicative_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_956_ == 0)
{
lean_object* v_unused_957_; 
v_unused_957_ = lean_ctor_get(v___x_894_, 1);
lean_dec(v_unused_957_);
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_956_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_toApplicative_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_956_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_toFunctor_899_; lean_object* v_toSeq_900_; lean_object* v_toSeqLeft_901_; lean_object* v_toSeqRight_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_954_; 
v_toFunctor_899_ = lean_ctor_get(v_toApplicative_895_, 0);
v_toSeq_900_ = lean_ctor_get(v_toApplicative_895_, 2);
v_toSeqLeft_901_ = lean_ctor_get(v_toApplicative_895_, 3);
v_toSeqRight_902_ = lean_ctor_get(v_toApplicative_895_, 4);
v_isSharedCheck_954_ = !lean_is_exclusive(v_toApplicative_895_);
if (v_isSharedCheck_954_ == 0)
{
lean_object* v_unused_955_; 
v_unused_955_ = lean_ctor_get(v_toApplicative_895_, 1);
lean_dec(v_unused_955_);
v___x_904_ = v_toApplicative_895_;
v_isShared_905_ = v_isSharedCheck_954_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_toSeqRight_902_);
lean_inc(v_toSeqLeft_901_);
lean_inc(v_toSeq_900_);
lean_inc(v_toFunctor_899_);
lean_dec(v_toApplicative_895_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_954_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___f_906_; lean_object* v___f_907_; lean_object* v___f_908_; lean_object* v___f_909_; lean_object* v___x_910_; lean_object* v___f_911_; lean_object* v___f_912_; lean_object* v___f_913_; lean_object* v___x_915_; 
v___f_906_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__1));
v___f_907_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__2));
lean_inc_ref(v_toFunctor_899_);
v___f_908_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_908_, 0, v_toFunctor_899_);
v___f_909_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_909_, 0, v_toFunctor_899_);
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v___f_908_);
lean_ctor_set(v___x_910_, 1, v___f_909_);
v___f_911_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_911_, 0, v_toSeqRight_902_);
v___f_912_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_912_, 0, v_toSeqLeft_901_);
v___f_913_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_913_, 0, v_toSeq_900_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 4, v___f_911_);
lean_ctor_set(v___x_904_, 3, v___f_912_);
lean_ctor_set(v___x_904_, 2, v___f_913_);
lean_ctor_set(v___x_904_, 1, v___f_906_);
lean_ctor_set(v___x_904_, 0, v___x_910_);
v___x_915_ = v___x_904_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_910_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v___f_906_);
lean_ctor_set(v_reuseFailAlloc_953_, 2, v___f_913_);
lean_ctor_set(v_reuseFailAlloc_953_, 3, v___f_912_);
lean_ctor_set(v_reuseFailAlloc_953_, 4, v___f_911_);
v___x_915_ = v_reuseFailAlloc_953_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_917_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 1, v___f_907_);
lean_ctor_set(v___x_897_, 0, v___x_915_);
v___x_917_ = v___x_897_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v___f_907_);
v___x_917_ = v_reuseFailAlloc_952_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_918_; lean_object* v_toApplicative_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_950_; 
v___x_918_ = l_StateRefT_x27_instMonad___redArg(v___x_917_);
v_toApplicative_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v___x_918_, 1);
lean_dec(v_unused_951_);
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_950_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_toApplicative_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_950_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v_toFunctor_923_; lean_object* v_toSeq_924_; lean_object* v_toSeqLeft_925_; lean_object* v_toSeqRight_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_948_; 
v_toFunctor_923_ = lean_ctor_get(v_toApplicative_919_, 0);
v_toSeq_924_ = lean_ctor_get(v_toApplicative_919_, 2);
v_toSeqLeft_925_ = lean_ctor_get(v_toApplicative_919_, 3);
v_toSeqRight_926_ = lean_ctor_get(v_toApplicative_919_, 4);
v_isSharedCheck_948_ = !lean_is_exclusive(v_toApplicative_919_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v_toApplicative_919_, 1);
lean_dec(v_unused_949_);
v___x_928_ = v_toApplicative_919_;
v_isShared_929_ = v_isSharedCheck_948_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_toSeqRight_926_);
lean_inc(v_toSeqLeft_925_);
lean_inc(v_toSeq_924_);
lean_inc(v_toFunctor_923_);
lean_dec(v_toApplicative_919_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_948_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___f_930_; lean_object* v___f_931_; lean_object* v___f_932_; lean_object* v___f_933_; lean_object* v___x_934_; lean_object* v___f_935_; lean_object* v___f_936_; lean_object* v___f_937_; lean_object* v___x_939_; 
v___f_930_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__3));
v___f_931_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__4));
lean_inc_ref(v_toFunctor_923_);
v___f_932_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_932_, 0, v_toFunctor_923_);
v___f_933_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_933_, 0, v_toFunctor_923_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v___f_932_);
lean_ctor_set(v___x_934_, 1, v___f_933_);
v___f_935_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_935_, 0, v_toSeqRight_926_);
v___f_936_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_936_, 0, v_toSeqLeft_925_);
v___f_937_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_937_, 0, v_toSeq_924_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 4, v___f_935_);
lean_ctor_set(v___x_928_, 3, v___f_936_);
lean_ctor_set(v___x_928_, 2, v___f_937_);
lean_ctor_set(v___x_928_, 1, v___f_930_);
lean_ctor_set(v___x_928_, 0, v___x_934_);
v___x_939_ = v___x_928_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v___f_930_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v___f_937_);
lean_ctor_set(v_reuseFailAlloc_947_, 3, v___f_936_);
lean_ctor_set(v_reuseFailAlloc_947_, 4, v___f_935_);
v___x_939_ = v_reuseFailAlloc_947_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_941_; 
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 1, v___f_931_);
lean_ctor_set(v___x_921_, 0, v___x_939_);
v___x_941_ = v___x_921_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v___f_931_);
v___x_941_ = v_reuseFailAlloc_946_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_16397__overap_944_; lean_object* v___x_945_; 
v___x_942_ = lean_box(0);
v___x_943_ = l_instInhabitedOfMonad___redArg(v___x_941_, v___x_942_);
v___x_16397__overap_944_ = lean_panic_fn_borrowed(v___x_943_, v_msg_887_);
lean_dec(v___x_943_);
lean_inc(v___y_891_);
lean_inc_ref(v___y_890_);
lean_inc(v___y_889_);
lean_inc_ref(v___y_888_);
v___x_945_ = lean_apply_5(v___x_16397__overap_944_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, lean_box(0));
return v___x_945_;
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
LEAN_EXPORT void l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_887_ = stack[0].m_obj;
lean_object* v___y_888_ = stack[1].m_obj;
lean_object* v___y_889_ = stack[2].m_obj;
lean_object* v___y_890_ = stack[3].m_obj;
lean_object* v___y_891_ = stack[4].m_obj;
lean_object* v_res_958_;
v_res_958_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(v_msg_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
stack->m_obj
 = v_res_958_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___boxed(lean_object* v_msg_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(v_msg_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
return v_res_965_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__0));
v___x_968_ = l_Lean_stringToMessageData(v___x_967_);
return v___x_968_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__2));
v___x_971_ = l_Lean_stringToMessageData(v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_975_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6));
v___x_976_ = lean_unsigned_to_nat(11u);
v___x_977_ = lean_unsigned_to_nat(122u);
v___x_978_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__5));
v___x_979_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__4));
v___x_980_ = l_mkPanicMessageWithDecl(v___x_979_, v___x_978_, v___x_977_, v___x_976_, v___x_975_);
return v___x_980_;
}
}
lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(lean_object* v_constName_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_995_; lean_object* v_env_996_; uint8_t v___x_997_; lean_object* v___x_998_; 
v___x_995_ = lean_st_ref_get(v___y_985_);
v_env_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc_ref(v_env_996_);
lean_dec(v___x_995_);
v___x_997_ = 0;
lean_inc(v_constName_981_);
v___x_998_ = l_Lean_Environment_findAsync_x3f(v_env_996_, v_constName_981_, v___x_997_);
if (lean_obj_tag(v___x_998_) == 1)
{
lean_object* v_val_999_; uint8_t v_kind_1000_; 
v_val_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_val_999_);
lean_dec_ref_known(v___x_998_, 1);
v_kind_1000_ = lean_ctor_get_uint8(v_val_999_, sizeof(void*)*3);
if (v_kind_1000_ == 6)
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_999_);
if (lean_obj_tag(v___x_1001_) == 6)
{
lean_object* v_val_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_dec(v_constName_981_);
v_val_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_val_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
lean_ctor_set_tag(v___x_1004_, 0);
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_val_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_dec_ref(v___x_1001_);
v___x_1010_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7);
v___x_1011_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(v___x_1010_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1020_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1014_ = v___x_1011_;
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1011_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
if (lean_obj_tag(v_a_1012_) == 0)
{
lean_del_object(v___x_1014_);
goto v___jp_987_;
}
else
{
lean_object* v_val_1016_; lean_object* v___x_1018_; 
lean_dec(v_constName_981_);
v_val_1016_ = lean_ctor_get(v_a_1012_, 0);
lean_inc(v_val_1016_);
lean_dec_ref_known(v_a_1012_, 1);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v_val_1016_);
v___x_1018_ = v___x_1014_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_val_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_dec(v_constName_981_);
v_a_1021_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1011_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1011_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
else
{
lean_dec(v_val_999_);
goto v___jp_987_;
}
}
else
{
lean_dec(v___x_998_);
goto v___jp_987_;
}
v___jp_987_:
{
lean_object* v___x_988_; uint8_t v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_988_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1);
v___x_989_ = 0;
v___x_990_ = l_Lean_MessageData_ofConstName(v_constName_981_, v___x_989_);
v___x_991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_988_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3);
v___x_993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_991_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v___x_993_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
return v___x_994_;
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_981_ = stack[0].m_obj;
lean_object* v___y_982_ = stack[1].m_obj;
lean_object* v___y_983_ = stack[2].m_obj;
lean_object* v___y_984_ = stack[3].m_obj;
lean_object* v___y_985_ = stack[4].m_obj;
lean_object* v_res_1029_;
v_res_1029_ = l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(v_constName_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
stack->m_obj
 = v_res_1029_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___boxed(lean_object* v_constName_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(v_constName_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1036_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(uint8_t v___x_1037_, lean_object* v___x_1038_, lean_object* v_as_x27_1039_, lean_object* v_b_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
if (lean_obj_tag(v_as_x27_1039_) == 0)
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1046_, 0, v_b_1040_);
return v___x_1046_;
}
else
{
lean_object* v_head_1047_; lean_object* v_tail_1048_; uint8_t v___x_1049_; uint8_t v___x_1050_; lean_object* v___x_1051_; 
v_head_1047_ = lean_ctor_get(v_as_x27_1039_, 0);
v_tail_1048_ = lean_ctor_get(v_as_x27_1039_, 1);
v___x_1049_ = 0;
v___x_1050_ = 1;
lean_inc(v_head_1047_);
v___x_1051_ = l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(v_head_1047_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v_a_1052_; lean_object* v_toConstantVal_1053_; lean_object* v_cidx_1054_; lean_object* v_numFields_1055_; lean_object* v_type_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___f_1060_; lean_object* v___x_1061_; 
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1052_);
lean_dec_ref_known(v___x_1051_, 1);
v_toConstantVal_1053_ = lean_ctor_get(v_a_1052_, 0);
lean_inc_ref(v_toConstantVal_1053_);
v_cidx_1054_ = lean_ctor_get(v_a_1052_, 2);
lean_inc(v_cidx_1054_);
v_numFields_1055_ = lean_ctor_get(v_a_1052_, 4);
lean_inc(v_numFields_1055_);
lean_dec(v_a_1052_);
v_type_1056_ = lean_ctor_get(v_toConstantVal_1053_, 2);
lean_inc_ref(v_type_1056_);
lean_dec_ref(v_toConstantVal_1053_);
v___x_1057_ = lean_box(v___x_1049_);
v___x_1058_ = lean_box(v___x_1037_);
v___x_1059_ = lean_box(v___x_1050_);
v___f_1060_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1060_, 0, v_cidx_1054_);
lean_closure_set(v___f_1060_, 1, v___x_1057_);
lean_closure_set(v___f_1060_, 2, v___x_1058_);
lean_closure_set(v___f_1060_, 3, v___x_1059_);
v___x_1061_ = l_Lean_Meta_instantiateForall(v_type_1056_, v___x_1038_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1073_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1064_ = v___x_1061_;
v_isShared_1065_ = v_isSharedCheck_1073_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1073_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
lean_ctor_set_tag(v___x_1064_, 1);
lean_ctor_set(v___x_1064_, 0, v_numFields_1055_);
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_numFields_1055_);
v___x_1067_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_a_1062_, v___x_1067_, v___f_1060_, v___x_1049_, v___x_1049_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1070_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1070_ = l_Lean_Expr_app___override(v_b_1040_, v_a_1069_);
v_as_x27_1039_ = v_tail_1048_;
v_b_1040_ = v___x_1070_;
goto _start;
}
else
{
lean_dec_ref(v_b_1040_);
return v___x_1068_;
}
}
}
}
else
{
lean_dec_ref(v___f_1060_);
lean_dec(v_numFields_1055_);
lean_dec_ref(v_b_1040_);
return v___x_1061_;
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
lean_dec_ref(v_b_1040_);
v_a_1074_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1051_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1051_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1037_ = stack[0].m_num;
lean_object* v___x_1038_ = stack[1].m_obj;
lean_object* v_as_x27_1039_ = stack[2].m_obj;
lean_object* v_b_1040_ = stack[3].m_obj;
lean_object* v___y_1041_ = stack[4].m_obj;
lean_object* v___y_1042_ = stack[5].m_obj;
lean_object* v___y_1043_ = stack[6].m_obj;
lean_object* v___y_1044_ = stack[7].m_obj;
lean_object* v_res_1082_;
v_res_1082_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_1037_, v___x_1038_, v_as_x27_1039_, v_b_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
stack->m_obj
 = v_res_1082_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___boxed(lean_object* v___x_1083_, lean_object* v___x_1084_, lean_object* v_as_x27_1085_, lean_object* v_b_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
uint8_t v___x_21086__boxed_1092_; lean_object* v_res_1093_; 
v___x_21086__boxed_1092_ = lean_unbox(v___x_1083_);
v_res_1093_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_21086__boxed_1092_, v___x_1084_, v_as_x27_1085_, v_b_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v_as_x27_1085_);
lean_dec_ref(v___x_1084_);
return v_res_1093_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = lean_box(0);
v___x_1095_ = l_Lean_Level_succ___override(v___x_1094_);
return v___x_1095_;
}
}
lean_object* l_Lean_mkCtorIdx___lam__0(lean_object* v_xs_1096_, uint8_t v___x_1097_, uint8_t v___x_1098_, uint8_t v___x_1099_, lean_object* v_val_1100_, lean_object* v___x_1101_, lean_object* v___x_1102_, lean_object* v___x_1103_, lean_object* v___x_1104_, lean_object* v___x_1105_, lean_object* v_ctors_1106_, lean_object* v___x_1107_, lean_object* v_x_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_value_1115_; lean_object* v___x_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1118_ = l_Lean_InductiveVal_numCtors(v_val_1100_);
v___x_1119_ = lean_unsigned_to_nat(1u);
v___x_1120_ = lean_nat_dec_eq(v___x_1118_, v___x_1119_);
lean_dec(v___x_1118_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_dec(v___x_1107_);
lean_inc_ref(v_x_1108_);
lean_inc_ref(v___x_1101_);
v___x_1121_ = lean_array_push(v___x_1101_, v_x_1108_);
v___x_1122_ = l_Lean_Meta_mkLambdaFVars(v___x_1121_, v___x_1102_, v___x_1097_, v___x_1098_, v___x_1097_, v___x_1098_, v___x_1099_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec_ref(v___x_1121_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v___x_1122_, 1);
v___x_1124_ = lean_obj_once(&l_Lean_mkCtorIdx___lam__0___closed__0, &l_Lean_mkCtorIdx___lam__0___closed__0_once, _init_l_Lean_mkCtorIdx___lam__0___closed__0);
v___x_1125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1124_);
lean_ctor_set(v___x_1125_, 1, v___x_1103_);
v___x_1126_ = l_Lean_mkConst(v___x_1104_, v___x_1125_);
v___x_1127_ = l_Lean_mkAppN(v___x_1126_, v___x_1105_);
v___x_1128_ = l_Lean_Expr_app___override(v___x_1127_, v_a_1123_);
v___x_1129_ = l_Lean_mkAppN(v___x_1128_, v___x_1101_);
lean_dec_ref(v___x_1101_);
lean_inc_ref(v_x_1108_);
v___x_1130_ = l_Lean_Expr_app___override(v___x_1129_, v_x_1108_);
v___x_1131_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_1098_, v___x_1105_, v_ctors_1106_, v___x_1130_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1132_);
lean_dec_ref_known(v___x_1131_, 1);
v_value_1115_ = v_a_1132_;
goto v___jp_1114_;
}
else
{
lean_dec_ref(v_x_1108_);
lean_dec_ref(v_xs_1096_);
return v___x_1131_;
}
}
else
{
lean_dec_ref(v_x_1108_);
lean_dec(v___x_1104_);
lean_dec(v___x_1103_);
lean_dec_ref(v___x_1101_);
lean_dec_ref(v_xs_1096_);
return v___x_1122_;
}
}
else
{
lean_object* v___x_1133_; 
lean_dec(v___x_1104_);
lean_dec(v___x_1103_);
lean_dec_ref(v___x_1102_);
lean_dec_ref(v___x_1101_);
v___x_1133_ = l_Lean_mkRawNatLit(v___x_1107_);
v_value_1115_ = v___x_1133_;
goto v___jp_1114_;
}
v___jp_1114_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = lean_array_push(v_xs_1096_, v_x_1108_);
v___x_1117_ = l_Lean_Meta_mkLambdaFVars(v___x_1116_, v_value_1115_, v___x_1097_, v___x_1098_, v___x_1097_, v___x_1098_, v___x_1099_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec_ref(v___x_1116_);
return v___x_1117_;
}
}
}
LEAN_EXPORT void l_Lean_mkCtorIdx___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1096_ = stack[0].m_obj;
uint8_t v___x_1097_ = stack[1].m_num;
uint8_t v___x_1098_ = stack[2].m_num;
uint8_t v___x_1099_ = stack[3].m_num;
lean_object* v_val_1100_ = stack[4].m_obj;
lean_object* v___x_1101_ = stack[5].m_obj;
lean_object* v___x_1102_ = stack[6].m_obj;
lean_object* v___x_1103_ = stack[7].m_obj;
lean_object* v___x_1104_ = stack[8].m_obj;
lean_object* v___x_1105_ = stack[9].m_obj;
lean_object* v_ctors_1106_ = stack[10].m_obj;
lean_object* v___x_1107_ = stack[11].m_obj;
lean_object* v_x_1108_ = stack[12].m_obj;
lean_object* v___y_1109_ = stack[13].m_obj;
lean_object* v___y_1110_ = stack[14].m_obj;
lean_object* v___y_1111_ = stack[15].m_obj;
lean_object* v___y_1112_ = stack[16].m_obj;
lean_object* v_res_1134_;
v_res_1134_ = l_Lean_mkCtorIdx___lam__0(v_xs_1096_, v___x_1097_, v___x_1098_, v___x_1099_, v_val_1100_, v___x_1101_, v___x_1102_, v___x_1103_, v___x_1104_, v___x_1105_, v_ctors_1106_, v___x_1107_, v_x_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
stack->m_obj
 = v_res_1134_;
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0___boxed(lean_object** _args){
lean_object* v_xs_1135_ = _args[0];
lean_object* v___x_1136_ = _args[1];
lean_object* v___x_1137_ = _args[2];
lean_object* v___x_1138_ = _args[3];
lean_object* v_val_1139_ = _args[4];
lean_object* v___x_1140_ = _args[5];
lean_object* v___x_1141_ = _args[6];
lean_object* v___x_1142_ = _args[7];
lean_object* v___x_1143_ = _args[8];
lean_object* v___x_1144_ = _args[9];
lean_object* v_ctors_1145_ = _args[10];
lean_object* v___x_1146_ = _args[11];
lean_object* v_x_1147_ = _args[12];
lean_object* v___y_1148_ = _args[13];
lean_object* v___y_1149_ = _args[14];
lean_object* v___y_1150_ = _args[15];
lean_object* v___y_1151_ = _args[16];
lean_object* v___y_1152_ = _args[17];
_start:
{
uint8_t v___x_21223__boxed_1153_; uint8_t v___x_21224__boxed_1154_; uint8_t v___x_21225__boxed_1155_; lean_object* v_res_1156_; 
v___x_21223__boxed_1153_ = lean_unbox(v___x_1136_);
v___x_21224__boxed_1154_ = lean_unbox(v___x_1137_);
v___x_21225__boxed_1155_ = lean_unbox(v___x_1138_);
v_res_1156_ = l_Lean_mkCtorIdx___lam__0(v_xs_1135_, v___x_21223__boxed_1153_, v___x_21224__boxed_1154_, v___x_21225__boxed_1155_, v_val_1139_, v___x_1140_, v___x_1141_, v___x_1142_, v___x_1143_, v___x_1144_, v_ctors_1145_, v___x_1146_, v_x_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v_ctors_1145_);
lean_dec_ref(v___x_1144_);
lean_dec_ref(v_val_1139_);
return v_res_1156_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(lean_object* v_k_1157_, lean_object* v_b_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___x_1164_; 
lean_inc(v___y_1162_);
lean_inc_ref(v___y_1161_);
lean_inc(v___y_1160_);
lean_inc_ref(v___y_1159_);
v___x_1164_ = lean_apply_6(v_k_1157_, v_b_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, lean_box(0));
return v___x_1164_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1157_ = stack[0].m_obj;
lean_object* v_b_1158_ = stack[1].m_obj;
lean_object* v___y_1159_ = stack[2].m_obj;
lean_object* v___y_1160_ = stack[3].m_obj;
lean_object* v___y_1161_ = stack[4].m_obj;
lean_object* v___y_1162_ = stack[5].m_obj;
lean_object* v_res_1165_;
v_res_1165_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(v_k_1157_, v_b_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
stack->m_obj
 = v_res_1165_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(lean_object* v_k_1166_, lean_object* v_b_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(v_k_1166_, v_b_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
return v_res_1173_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(lean_object* v_name_1174_, uint8_t v_bi_1175_, lean_object* v_type_1176_, lean_object* v_k_1177_, uint8_t v_kind_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___f_1184_; lean_object* v___x_1185_; 
v___f_1184_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1184_, 0, v_k_1177_);
v___x_1185_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1174_, v_bi_1175_, v_type_1176_, v___f_1184_, v_kind_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
v_a_1194_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1185_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1185_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1174_ = stack[0].m_obj;
uint8_t v_bi_1175_ = stack[1].m_num;
lean_object* v_type_1176_ = stack[2].m_obj;
lean_object* v_k_1177_ = stack[3].m_obj;
uint8_t v_kind_1178_ = stack[4].m_num;
lean_object* v___y_1179_ = stack[5].m_obj;
lean_object* v___y_1180_ = stack[6].m_obj;
lean_object* v___y_1181_ = stack[7].m_obj;
lean_object* v___y_1182_ = stack[8].m_obj;
lean_object* v_res_1202_;
v_res_1202_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_1174_, v_bi_1175_, v_type_1176_, v_k_1177_, v_kind_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
stack->m_obj
 = v_res_1202_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___boxed(lean_object* v_name_1203_, lean_object* v_bi_1204_, lean_object* v_type_1205_, lean_object* v_k_1206_, lean_object* v_kind_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
uint8_t v_bi_boxed_1213_; uint8_t v_kind_boxed_1214_; lean_object* v_res_1215_; 
v_bi_boxed_1213_ = lean_unbox(v_bi_1204_);
v_kind_boxed_1214_ = lean_unbox(v_kind_1207_);
v_res_1215_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_1203_, v_bi_boxed_1213_, v_type_1205_, v_k_1206_, v_kind_boxed_1214_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
return v_res_1215_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(lean_object* v_name_1216_, lean_object* v_type_1217_, lean_object* v_k_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
uint8_t v___x_1224_; uint8_t v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = 0;
v___x_1225_ = 0;
v___x_1226_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_1216_, v___x_1224_, v_type_1217_, v_k_1218_, v___x_1225_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
return v___x_1226_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1216_ = stack[0].m_obj;
lean_object* v_type_1217_ = stack[1].m_obj;
lean_object* v_k_1218_ = stack[2].m_obj;
lean_object* v___y_1219_ = stack[3].m_obj;
lean_object* v___y_1220_ = stack[4].m_obj;
lean_object* v___y_1221_ = stack[5].m_obj;
lean_object* v___y_1222_ = stack[6].m_obj;
lean_object* v_res_1227_;
v_res_1227_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v_name_1216_, v_type_1217_, v_k_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
stack->m_obj
 = v_res_1227_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg___boxed(lean_object* v_name_1228_, lean_object* v_type_1229_, lean_object* v_k_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v_name_1228_, v_type_1229_, v_k_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
return v_res_1236_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(lean_object* v_env_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v___x_1241_; lean_object* v_nextMacroScope_1242_; lean_object* v_ngen_1243_; lean_object* v_auxDeclNGen_1244_; lean_object* v_traceState_1245_; lean_object* v_recordedDeps_1246_; lean_object* v_messages_1247_; lean_object* v_infoState_1248_; lean_object* v_snapshotTasks_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1275_; 
v___x_1241_ = lean_st_ref_take(v___y_1239_);
v_nextMacroScope_1242_ = lean_ctor_get(v___x_1241_, 1);
v_ngen_1243_ = lean_ctor_get(v___x_1241_, 2);
v_auxDeclNGen_1244_ = lean_ctor_get(v___x_1241_, 3);
v_traceState_1245_ = lean_ctor_get(v___x_1241_, 4);
v_recordedDeps_1246_ = lean_ctor_get(v___x_1241_, 6);
v_messages_1247_ = lean_ctor_get(v___x_1241_, 7);
v_infoState_1248_ = lean_ctor_get(v___x_1241_, 8);
v_snapshotTasks_1249_ = lean_ctor_get(v___x_1241_, 9);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1275_ == 0)
{
lean_object* v_unused_1276_; lean_object* v_unused_1277_; 
v_unused_1276_ = lean_ctor_get(v___x_1241_, 5);
lean_dec(v_unused_1276_);
v_unused_1277_ = lean_ctor_get(v___x_1241_, 0);
lean_dec(v_unused_1277_);
v___x_1251_ = v___x_1241_;
v_isShared_1252_ = v_isSharedCheck_1275_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_snapshotTasks_1249_);
lean_inc(v_infoState_1248_);
lean_inc(v_messages_1247_);
lean_inc(v_recordedDeps_1246_);
lean_inc(v_traceState_1245_);
lean_inc(v_auxDeclNGen_1244_);
lean_inc(v_ngen_1243_);
lean_inc(v_nextMacroScope_1242_);
lean_dec(v___x_1241_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1275_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1253_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 5, v___x_1253_);
lean_ctor_set(v___x_1251_, 0, v_env_1237_);
v___x_1255_ = v___x_1251_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_env_1237_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_nextMacroScope_1242_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v_ngen_1243_);
lean_ctor_set(v_reuseFailAlloc_1274_, 3, v_auxDeclNGen_1244_);
lean_ctor_set(v_reuseFailAlloc_1274_, 4, v_traceState_1245_);
lean_ctor_set(v_reuseFailAlloc_1274_, 5, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1274_, 6, v_recordedDeps_1246_);
lean_ctor_set(v_reuseFailAlloc_1274_, 7, v_messages_1247_);
lean_ctor_set(v_reuseFailAlloc_1274_, 8, v_infoState_1248_);
lean_ctor_set(v_reuseFailAlloc_1274_, 9, v_snapshotTasks_1249_);
v___x_1255_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v_mctx_1258_; lean_object* v_zetaDeltaFVarIds_1259_; lean_object* v_postponed_1260_; lean_object* v_diag_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1272_; 
v___x_1256_ = lean_st_ref_put(v___y_1239_, v___x_1255_);
v___x_1257_ = lean_st_ref_take(v___y_1238_);
v_mctx_1258_ = lean_ctor_get(v___x_1257_, 0);
v_zetaDeltaFVarIds_1259_ = lean_ctor_get(v___x_1257_, 2);
v_postponed_1260_ = lean_ctor_get(v___x_1257_, 3);
v_diag_1261_ = lean_ctor_get(v___x_1257_, 4);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1272_ == 0)
{
lean_object* v_unused_1273_; 
v_unused_1273_ = lean_ctor_get(v___x_1257_, 1);
lean_dec(v_unused_1273_);
v___x_1263_ = v___x_1257_;
v_isShared_1264_ = v_isSharedCheck_1272_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_diag_1261_);
lean_inc(v_postponed_1260_);
lean_inc(v_zetaDeltaFVarIds_1259_);
lean_inc(v_mctx_1258_);
lean_dec(v___x_1257_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1272_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1268_; 
v___x_1265_ = lean_box(0);
v___x_1266_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 1, v___x_1266_);
v___x_1268_ = v___x_1263_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_mctx_1258_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1271_, 2, v_zetaDeltaFVarIds_1259_);
lean_ctor_set(v_reuseFailAlloc_1271_, 3, v_postponed_1260_);
lean_ctor_set(v_reuseFailAlloc_1271_, 4, v_diag_1261_);
v___x_1268_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = lean_st_ref_put(v___y_1238_, v___x_1268_);
v___x_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1265_);
return v___x_1270_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1237_ = stack[0].m_obj;
lean_object* v___y_1238_ = stack[1].m_obj;
lean_object* v___y_1239_ = stack[2].m_obj;
lean_object* v_res_1278_;
v_res_1278_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(v_env_1237_, v___y_1238_, v___y_1239_);
stack->m_obj
 = v_res_1278_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg___boxed(lean_object* v_env_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(v_env_1279_, v___y_1280_, v___y_1281_);
lean_dec(v___y_1281_);
lean_dec(v___y_1280_);
return v_res_1283_;
}
}
lean_object* l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9(lean_object* v_declName_1284_, lean_object* v_impName_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; lean_object* v_env_1292_; lean_object* v___x_1293_; 
v___x_1291_ = lean_st_ref_get(v___y_1289_);
v_env_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc_ref(v_env_1292_);
lean_dec(v___x_1291_);
v___x_1293_ = l_Lean_Compiler_setImplementedBy(v_env_1292_, v_declName_1284_, v_impName_1285_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1303_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1303_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1303_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
lean_ctor_set_tag(v___x_1296_, 3);
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = l_Lean_MessageData_ofFormat(v___x_1299_);
v___x_1301_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v___x_1300_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
return v___x_1301_;
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1305_; 
v_a_1304_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1293_, 1);
v___x_1305_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(v_a_1304_, v___y_1287_, v___y_1289_);
return v___x_1305_;
}
}
}
LEAN_EXPORT void l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1284_ = stack[0].m_obj;
lean_object* v_impName_1285_ = stack[1].m_obj;
lean_object* v___y_1286_ = stack[2].m_obj;
lean_object* v___y_1287_ = stack[3].m_obj;
lean_object* v___y_1288_ = stack[4].m_obj;
lean_object* v___y_1289_ = stack[5].m_obj;
lean_object* v_res_1306_;
v_res_1306_ = l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9(v_declName_1284_, v_impName_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
stack->m_obj
 = v_res_1306_;
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9___boxed(lean_object* v_declName_1307_, lean_object* v_impName_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9(v_declName_1307_, v_impName_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
return v_res_1314_;
}
}
lean_object* l_Lean_mkCtorIdx___lam__1(lean_object* v___x_1318_, lean_object* v___x_1319_, lean_object* v_xs_1320_, uint8_t v___x_1321_, uint8_t v___x_1322_, lean_object* v_val_1323_, lean_object* v___x_1324_, lean_object* v___x_1325_, lean_object* v___x_1326_, lean_object* v___x_1327_, lean_object* v_ctors_1328_, lean_object* v___x_1329_, lean_object* v___x_1330_, lean_object* v_levelParams_1331_, lean_object* v_indName_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v___x_1338_; 
lean_inc_ref(v___x_1319_);
lean_inc_ref(v___x_1318_);
v___x_1338_ = l_Lean_mkArrow(v___x_1318_, v___x_1319_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; uint8_t v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___f_1344_; lean_object* v___x_1345_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1339_);
lean_dec_ref_known(v___x_1338_, 1);
v___x_1340_ = 1;
v___x_1341_ = lean_box(v___x_1321_);
v___x_1342_ = lean_box(v___x_1322_);
v___x_1343_ = lean_box(v___x_1340_);
lean_inc_ref(v_val_1323_);
lean_inc_ref(v_xs_1320_);
v___f_1344_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1344_, 0, v_xs_1320_);
lean_closure_set(v___f_1344_, 1, v___x_1341_);
lean_closure_set(v___f_1344_, 2, v___x_1342_);
lean_closure_set(v___f_1344_, 3, v___x_1343_);
lean_closure_set(v___f_1344_, 4, v_val_1323_);
lean_closure_set(v___f_1344_, 5, v___x_1324_);
lean_closure_set(v___f_1344_, 6, v___x_1319_);
lean_closure_set(v___f_1344_, 7, v___x_1325_);
lean_closure_set(v___f_1344_, 8, v___x_1326_);
lean_closure_set(v___f_1344_, 9, v___x_1327_);
lean_closure_set(v___f_1344_, 10, v_ctors_1328_);
lean_closure_set(v___f_1344_, 11, v___x_1329_);
v___x_1345_ = l_Lean_Meta_mkForallFVars(v_xs_1320_, v_a_1339_, v___x_1321_, v___x_1322_, v___x_1322_, v___x_1340_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
lean_dec_ref(v_xs_1320_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
v___x_1347_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__1___closed__1));
v___x_1348_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v___x_1347_, v___x_1318_, v___f_1344_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1350_; lean_object* v_env_1351_; uint32_t v___x_1352_; lean_object* v___x_1353_; uint32_t v___x_1354_; uint32_t v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1499_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc_n(v_a_1349_, 2);
lean_dec_ref_known(v___x_1348_, 1);
v___x_1350_ = lean_st_ref_get(v___y_1336_);
v_env_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc_ref(v_env_1351_);
lean_dec(v___x_1350_);
v___x_1352_ = l_Lean_getMaxHeight(v_env_1351_, v_a_1349_);
v___x_1353_ = lean_unsigned_to_nat(1u);
v___x_1354_ = 1;
v___x_1355_ = lean_uint32_add(v___x_1352_, v___x_1354_);
v___x_1356_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_1356_, 0, v___x_1355_);
lean_inc(v_a_1346_);
lean_inc(v_levelParams_1331_);
lean_inc(v___x_1330_);
v___x_1357_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v___x_1330_, v_levelParams_1331_, v_a_1346_, v_a_1349_, v___x_1356_, v___y_1336_);
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1499_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1499_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
lean_ctor_set_tag(v___x_1360_, 1);
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___x_1390_; 
lean_inc_ref(v___x_1363_);
v___x_1390_ = l_Lean_addDecl(v___x_1363_, v___x_1321_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v___x_1391_; lean_object* v_env_1392_; lean_object* v_nextMacroScope_1393_; lean_object* v_ngen_1394_; lean_object* v_auxDeclNGen_1395_; lean_object* v_traceState_1396_; lean_object* v_recordedDeps_1397_; lean_object* v_messages_1398_; lean_object* v_infoState_1399_; lean_object* v_snapshotTasks_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1496_; 
lean_dec_ref_known(v___x_1390_, 1);
v___x_1391_ = lean_st_ref_take(v___y_1336_);
v_env_1392_ = lean_ctor_get(v___x_1391_, 0);
v_nextMacroScope_1393_ = lean_ctor_get(v___x_1391_, 1);
v_ngen_1394_ = lean_ctor_get(v___x_1391_, 2);
v_auxDeclNGen_1395_ = lean_ctor_get(v___x_1391_, 3);
v_traceState_1396_ = lean_ctor_get(v___x_1391_, 4);
v_recordedDeps_1397_ = lean_ctor_get(v___x_1391_, 6);
v_messages_1398_ = lean_ctor_get(v___x_1391_, 7);
v_infoState_1399_ = lean_ctor_get(v___x_1391_, 8);
v_snapshotTasks_1400_ = lean_ctor_get(v___x_1391_, 9);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; 
v_unused_1497_ = lean_ctor_get(v___x_1391_, 5);
lean_dec(v_unused_1497_);
v___x_1402_ = v___x_1391_;
v_isShared_1403_ = v_isSharedCheck_1496_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_snapshotTasks_1400_);
lean_inc(v_infoState_1399_);
lean_inc(v_messages_1398_);
lean_inc(v_recordedDeps_1397_);
lean_inc(v_traceState_1396_);
lean_inc(v_auxDeclNGen_1395_);
lean_inc(v_ngen_1394_);
lean_inc(v_nextMacroScope_1393_);
lean_inc(v_env_1392_);
lean_dec(v___x_1391_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1496_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
lean_inc(v___x_1330_);
v___x_1404_ = l_Lean_Meta_addToCompletionBlackList(v_env_1392_, v___x_1330_);
v___x_1405_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 5, v___x_1405_);
lean_ctor_set(v___x_1402_, 0, v___x_1404_);
v___x_1407_ = v___x_1402_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_nextMacroScope_1393_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v_ngen_1394_);
lean_ctor_set(v_reuseFailAlloc_1495_, 3, v_auxDeclNGen_1395_);
lean_ctor_set(v_reuseFailAlloc_1495_, 4, v_traceState_1396_);
lean_ctor_set(v_reuseFailAlloc_1495_, 5, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1495_, 6, v_recordedDeps_1397_);
lean_ctor_set(v_reuseFailAlloc_1495_, 7, v_messages_1398_);
lean_ctor_set(v_reuseFailAlloc_1495_, 8, v_infoState_1399_);
lean_ctor_set(v_reuseFailAlloc_1495_, 9, v_snapshotTasks_1400_);
v___x_1407_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v_mctx_1410_; lean_object* v_zetaDeltaFVarIds_1411_; lean_object* v_postponed_1412_; lean_object* v_diag_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1493_; 
v___x_1408_ = lean_st_ref_put(v___y_1336_, v___x_1407_);
v___x_1409_ = lean_st_ref_take(v___y_1334_);
v_mctx_1410_ = lean_ctor_get(v___x_1409_, 0);
v_zetaDeltaFVarIds_1411_ = lean_ctor_get(v___x_1409_, 2);
v_postponed_1412_ = lean_ctor_get(v___x_1409_, 3);
v_diag_1413_ = lean_ctor_get(v___x_1409_, 4);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; 
v_unused_1494_ = lean_ctor_get(v___x_1409_, 1);
lean_dec(v_unused_1494_);
v___x_1415_ = v___x_1409_;
v_isShared_1416_ = v_isSharedCheck_1493_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_diag_1413_);
lean_inc(v_postponed_1412_);
lean_inc(v_zetaDeltaFVarIds_1411_);
lean_inc(v_mctx_1410_);
lean_dec(v___x_1409_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1493_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
v___x_1417_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 1, v___x_1417_);
v___x_1419_ = v___x_1415_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_mctx_1410_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1492_, 2, v_zetaDeltaFVarIds_1411_);
lean_ctor_set(v_reuseFailAlloc_1492_, 3, v_postponed_1412_);
lean_ctor_set(v_reuseFailAlloc_1492_, 4, v_diag_1413_);
v___x_1419_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v_env_1422_; lean_object* v_nextMacroScope_1423_; lean_object* v_ngen_1424_; lean_object* v_auxDeclNGen_1425_; lean_object* v_traceState_1426_; lean_object* v_recordedDeps_1427_; lean_object* v_messages_1428_; lean_object* v_infoState_1429_; lean_object* v_snapshotTasks_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1490_; 
v___x_1420_ = lean_st_ref_put(v___y_1334_, v___x_1419_);
v___x_1421_ = lean_st_ref_take(v___y_1336_);
v_env_1422_ = lean_ctor_get(v___x_1421_, 0);
v_nextMacroScope_1423_ = lean_ctor_get(v___x_1421_, 1);
v_ngen_1424_ = lean_ctor_get(v___x_1421_, 2);
v_auxDeclNGen_1425_ = lean_ctor_get(v___x_1421_, 3);
v_traceState_1426_ = lean_ctor_get(v___x_1421_, 4);
v_recordedDeps_1427_ = lean_ctor_get(v___x_1421_, 6);
v_messages_1428_ = lean_ctor_get(v___x_1421_, 7);
v_infoState_1429_ = lean_ctor_get(v___x_1421_, 8);
v_snapshotTasks_1430_ = lean_ctor_get(v___x_1421_, 9);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1490_ == 0)
{
lean_object* v_unused_1491_; 
v_unused_1491_ = lean_ctor_get(v___x_1421_, 5);
lean_dec(v_unused_1491_);
v___x_1432_ = v___x_1421_;
v_isShared_1433_ = v_isSharedCheck_1490_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_snapshotTasks_1430_);
lean_inc(v_infoState_1429_);
lean_inc(v_messages_1428_);
lean_inc(v_recordedDeps_1427_);
lean_inc(v_traceState_1426_);
lean_inc(v_auxDeclNGen_1425_);
lean_inc(v_ngen_1424_);
lean_inc(v_nextMacroScope_1423_);
lean_inc(v_env_1422_);
lean_dec(v___x_1421_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1490_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1436_; 
lean_inc(v___x_1330_);
v___x_1434_ = l_Lean_addProtected(v_env_1422_, v___x_1330_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 5, v___x_1405_);
lean_ctor_set(v___x_1432_, 0, v___x_1434_);
v___x_1436_ = v___x_1432_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_nextMacroScope_1423_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v_ngen_1424_);
lean_ctor_set(v_reuseFailAlloc_1489_, 3, v_auxDeclNGen_1425_);
lean_ctor_set(v_reuseFailAlloc_1489_, 4, v_traceState_1426_);
lean_ctor_set(v_reuseFailAlloc_1489_, 5, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1489_, 6, v_recordedDeps_1427_);
lean_ctor_set(v_reuseFailAlloc_1489_, 7, v_messages_1428_);
lean_ctor_set(v_reuseFailAlloc_1489_, 8, v_infoState_1429_);
lean_ctor_set(v_reuseFailAlloc_1489_, 9, v_snapshotTasks_1430_);
v___x_1436_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v_mctx_1439_; lean_object* v_zetaDeltaFVarIds_1440_; lean_object* v_postponed_1441_; lean_object* v_diag_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1487_; 
v___x_1437_ = lean_st_ref_put(v___y_1336_, v___x_1436_);
v___x_1438_ = lean_st_ref_take(v___y_1334_);
v_mctx_1439_ = lean_ctor_get(v___x_1438_, 0);
v_zetaDeltaFVarIds_1440_ = lean_ctor_get(v___x_1438_, 2);
v_postponed_1441_ = lean_ctor_get(v___x_1438_, 3);
v_diag_1442_ = lean_ctor_get(v___x_1438_, 4);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1487_ == 0)
{
lean_object* v_unused_1488_; 
v_unused_1488_ = lean_ctor_get(v___x_1438_, 1);
lean_dec(v_unused_1488_);
v___x_1444_ = v___x_1438_;
v_isShared_1445_ = v_isSharedCheck_1487_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_diag_1442_);
lean_inc(v_postponed_1441_);
lean_inc(v_zetaDeltaFVarIds_1440_);
lean_inc(v_mctx_1439_);
lean_dec(v___x_1438_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1487_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 1, v___x_1417_);
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_mctx_1439_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1486_, 2, v_zetaDeltaFVarIds_1440_);
lean_ctor_set(v_reuseFailAlloc_1486_, 3, v_postponed_1441_);
lean_ctor_set(v_reuseFailAlloc_1486_, 4, v_diag_1442_);
v___x_1447_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v_env_1450_; uint8_t v___x_1451_; 
v___x_1448_ = lean_st_ref_put(v___y_1334_, v___x_1447_);
v___x_1449_ = lean_st_ref_get(v___y_1336_);
v_env_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc_ref(v_env_1450_);
lean_dec(v___x_1449_);
lean_inc(v_indName_1332_);
v___x_1451_ = l_Lean_isMarkedMeta(v_env_1450_, v_indName_1332_);
if (v___x_1451_ == 0)
{
v___y_1370_ = v___y_1333_;
v___y_1371_ = v___y_1334_;
v___y_1372_ = v___y_1335_;
v___y_1373_ = v___y_1336_;
goto v___jp_1369_;
}
else
{
lean_object* v___x_1452_; lean_object* v_env_1453_; lean_object* v_nextMacroScope_1454_; lean_object* v_ngen_1455_; lean_object* v_auxDeclNGen_1456_; lean_object* v_traceState_1457_; lean_object* v_recordedDeps_1458_; lean_object* v_messages_1459_; lean_object* v_infoState_1460_; lean_object* v_snapshotTasks_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1484_; 
v___x_1452_ = lean_st_ref_take(v___y_1336_);
v_env_1453_ = lean_ctor_get(v___x_1452_, 0);
v_nextMacroScope_1454_ = lean_ctor_get(v___x_1452_, 1);
v_ngen_1455_ = lean_ctor_get(v___x_1452_, 2);
v_auxDeclNGen_1456_ = lean_ctor_get(v___x_1452_, 3);
v_traceState_1457_ = lean_ctor_get(v___x_1452_, 4);
v_recordedDeps_1458_ = lean_ctor_get(v___x_1452_, 6);
v_messages_1459_ = lean_ctor_get(v___x_1452_, 7);
v_infoState_1460_ = lean_ctor_get(v___x_1452_, 8);
v_snapshotTasks_1461_ = lean_ctor_get(v___x_1452_, 9);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1484_ == 0)
{
lean_object* v_unused_1485_; 
v_unused_1485_ = lean_ctor_get(v___x_1452_, 5);
lean_dec(v_unused_1485_);
v___x_1463_ = v___x_1452_;
v_isShared_1464_ = v_isSharedCheck_1484_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_snapshotTasks_1461_);
lean_inc(v_infoState_1460_);
lean_inc(v_messages_1459_);
lean_inc(v_recordedDeps_1458_);
lean_inc(v_traceState_1457_);
lean_inc(v_auxDeclNGen_1456_);
lean_inc(v_ngen_1455_);
lean_inc(v_nextMacroScope_1454_);
lean_inc(v_env_1453_);
lean_dec(v___x_1452_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1484_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; lean_object* v___x_1467_; 
lean_inc(v___x_1330_);
v___x_1465_ = l_Lean_markMeta(v_env_1453_, v___x_1330_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 5, v___x_1405_);
lean_ctor_set(v___x_1463_, 0, v___x_1465_);
v___x_1467_ = v___x_1463_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1465_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_nextMacroScope_1454_);
lean_ctor_set(v_reuseFailAlloc_1483_, 2, v_ngen_1455_);
lean_ctor_set(v_reuseFailAlloc_1483_, 3, v_auxDeclNGen_1456_);
lean_ctor_set(v_reuseFailAlloc_1483_, 4, v_traceState_1457_);
lean_ctor_set(v_reuseFailAlloc_1483_, 5, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1483_, 6, v_recordedDeps_1458_);
lean_ctor_set(v_reuseFailAlloc_1483_, 7, v_messages_1459_);
lean_ctor_set(v_reuseFailAlloc_1483_, 8, v_infoState_1460_);
lean_ctor_set(v_reuseFailAlloc_1483_, 9, v_snapshotTasks_1461_);
v___x_1467_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v_mctx_1470_; lean_object* v_zetaDeltaFVarIds_1471_; lean_object* v_postponed_1472_; lean_object* v_diag_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1481_; 
v___x_1468_ = lean_st_ref_put(v___y_1336_, v___x_1467_);
v___x_1469_ = lean_st_ref_take(v___y_1334_);
v_mctx_1470_ = lean_ctor_get(v___x_1469_, 0);
v_zetaDeltaFVarIds_1471_ = lean_ctor_get(v___x_1469_, 2);
v_postponed_1472_ = lean_ctor_get(v___x_1469_, 3);
v_diag_1473_ = lean_ctor_get(v___x_1469_, 4);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; 
v_unused_1482_ = lean_ctor_get(v___x_1469_, 1);
lean_dec(v_unused_1482_);
v___x_1475_ = v___x_1469_;
v_isShared_1476_ = v_isSharedCheck_1481_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_diag_1473_);
lean_inc(v_postponed_1472_);
lean_inc(v_zetaDeltaFVarIds_1471_);
lean_inc(v_mctx_1470_);
lean_dec(v___x_1469_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1481_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v___x_1417_);
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_mctx_1470_);
lean_ctor_set(v_reuseFailAlloc_1480_, 1, v___x_1417_);
lean_ctor_set(v_reuseFailAlloc_1480_, 2, v_zetaDeltaFVarIds_1471_);
lean_ctor_set(v_reuseFailAlloc_1480_, 3, v_postponed_1472_);
lean_ctor_set(v_reuseFailAlloc_1480_, 4, v_diag_1473_);
v___x_1478_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_st_ref_put(v___y_1334_, v___x_1478_);
v___y_1370_ = v___y_1333_;
v___y_1371_ = v___y_1334_;
v___y_1372_ = v___y_1335_;
v___y_1373_ = v___y_1336_;
goto v___jp_1369_;
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
lean_dec_ref(v___x_1363_);
lean_dec(v_a_1346_);
lean_dec(v_indName_1332_);
lean_dec(v_levelParams_1331_);
lean_dec(v___x_1330_);
lean_dec_ref(v_val_1323_);
return v___x_1390_;
}
v___jp_1364_:
{
lean_object* v___x_1367_; 
v___x_1367_ = l_Lean_compileDecl(v___x_1363_, v___x_1322_, v___y_1365_, v___y_1366_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v___x_1368_; 
lean_dec_ref_known(v___x_1367_, 1);
v___x_1368_ = l_Lean_enableRealizationsForConst(v___x_1330_, v___y_1365_, v___y_1366_);
return v___x_1368_;
}
else
{
lean_dec(v___x_1330_);
return v___x_1367_;
}
}
v___jp_1369_:
{
lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1374_ = l_Lean_InductiveVal_numCtors(v_val_1323_);
lean_dec_ref(v_val_1323_);
v___x_1375_ = lean_nat_dec_eq(v___x_1374_, v___x_1353_);
lean_dec(v___x_1374_);
if (v___x_1375_ == 0)
{
uint8_t v___x_1376_; 
v___x_1376_ = l_Lean_Compiler_LCNF_isRuntimeBuiltinType(v_indName_1332_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; 
v___x_1377_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl(v_indName_1332_, v_levelParams_1331_, v_a_1346_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1379_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 1);
lean_inc(v___x_1330_);
v___x_1379_ = l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9(v___x_1330_, v_a_1378_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_dec_ref_known(v___x_1379_, 1);
v___y_1365_ = v___y_1372_;
v___y_1366_ = v___y_1373_;
goto v___jp_1364_;
}
else
{
lean_dec_ref(v___x_1363_);
lean_dec(v___x_1330_);
return v___x_1379_;
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec_ref(v___x_1363_);
lean_dec(v___x_1330_);
v_a_1380_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1377_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1377_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
else
{
lean_dec(v_a_1346_);
lean_dec(v_indName_1332_);
lean_dec(v_levelParams_1331_);
v___y_1365_ = v___y_1372_;
v___y_1366_ = v___y_1373_;
goto v___jp_1364_;
}
}
else
{
uint8_t v___x_1388_; lean_object* v___x_1389_; 
lean_dec(v_a_1346_);
lean_dec(v_indName_1332_);
lean_dec(v_levelParams_1331_);
v___x_1388_ = 2;
lean_inc(v___x_1330_);
v___x_1389_ = l_Lean_Meta_setInlineAttribute(v___x_1330_, v___x_1388_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_dec_ref_known(v___x_1389_, 1);
v___y_1365_ = v___y_1372_;
v___y_1366_ = v___y_1373_;
goto v___jp_1364_;
}
else
{
lean_dec_ref(v___x_1363_);
lean_dec(v___x_1330_);
return v___x_1389_;
}
}
}
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v_a_1346_);
lean_dec(v_indName_1332_);
lean_dec(v_levelParams_1331_);
lean_dec(v___x_1330_);
lean_dec_ref(v_val_1323_);
v_a_1500_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1348_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1348_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec_ref(v___f_1344_);
lean_dec(v_indName_1332_);
lean_dec(v_levelParams_1331_);
lean_dec(v___x_1330_);
lean_dec_ref(v_val_1323_);
lean_dec_ref(v___x_1318_);
v_a_1508_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1345_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1345_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1523_; 
lean_dec(v_indName_1332_);
lean_dec(v_levelParams_1331_);
lean_dec(v___x_1330_);
lean_dec(v___x_1329_);
lean_dec(v_ctors_1328_);
lean_dec_ref(v___x_1327_);
lean_dec(v___x_1326_);
lean_dec(v___x_1325_);
lean_dec_ref(v___x_1324_);
lean_dec_ref(v_val_1323_);
lean_dec_ref(v_xs_1320_);
lean_dec_ref(v___x_1319_);
lean_dec_ref(v___x_1318_);
v_a_1516_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1518_ = v___x_1338_;
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1338_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1523_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1521_; 
if (v_isShared_1519_ == 0)
{
v___x_1521_ = v___x_1518_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkCtorIdx___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1318_ = stack[0].m_obj;
lean_object* v___x_1319_ = stack[1].m_obj;
lean_object* v_xs_1320_ = stack[2].m_obj;
uint8_t v___x_1321_ = stack[3].m_num;
uint8_t v___x_1322_ = stack[4].m_num;
lean_object* v_val_1323_ = stack[5].m_obj;
lean_object* v___x_1324_ = stack[6].m_obj;
lean_object* v___x_1325_ = stack[7].m_obj;
lean_object* v___x_1326_ = stack[8].m_obj;
lean_object* v___x_1327_ = stack[9].m_obj;
lean_object* v_ctors_1328_ = stack[10].m_obj;
lean_object* v___x_1329_ = stack[11].m_obj;
lean_object* v___x_1330_ = stack[12].m_obj;
lean_object* v_levelParams_1331_ = stack[13].m_obj;
lean_object* v_indName_1332_ = stack[14].m_obj;
lean_object* v___y_1333_ = stack[15].m_obj;
lean_object* v___y_1334_ = stack[16].m_obj;
lean_object* v___y_1335_ = stack[17].m_obj;
lean_object* v___y_1336_ = stack[18].m_obj;
lean_object* v_res_1524_;
v_res_1524_ = l_Lean_mkCtorIdx___lam__1(v___x_1318_, v___x_1319_, v_xs_1320_, v___x_1321_, v___x_1322_, v_val_1323_, v___x_1324_, v___x_1325_, v___x_1326_, v___x_1327_, v_ctors_1328_, v___x_1329_, v___x_1330_, v_levelParams_1331_, v_indName_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
stack->m_obj
 = v_res_1524_;
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1___boxed(lean_object** _args){
lean_object* v___x_1525_ = _args[0];
lean_object* v___x_1526_ = _args[1];
lean_object* v_xs_1527_ = _args[2];
lean_object* v___x_1528_ = _args[3];
lean_object* v___x_1529_ = _args[4];
lean_object* v_val_1530_ = _args[5];
lean_object* v___x_1531_ = _args[6];
lean_object* v___x_1532_ = _args[7];
lean_object* v___x_1533_ = _args[8];
lean_object* v___x_1534_ = _args[9];
lean_object* v_ctors_1535_ = _args[10];
lean_object* v___x_1536_ = _args[11];
lean_object* v___x_1537_ = _args[12];
lean_object* v_levelParams_1538_ = _args[13];
lean_object* v_indName_1539_ = _args[14];
lean_object* v___y_1540_ = _args[15];
lean_object* v___y_1541_ = _args[16];
lean_object* v___y_1542_ = _args[17];
lean_object* v___y_1543_ = _args[18];
lean_object* v___y_1544_ = _args[19];
_start:
{
uint8_t v___x_21695__boxed_1545_; uint8_t v___x_21696__boxed_1546_; lean_object* v_res_1547_; 
v___x_21695__boxed_1545_ = lean_unbox(v___x_1528_);
v___x_21696__boxed_1546_ = lean_unbox(v___x_1529_);
v_res_1547_ = l_Lean_mkCtorIdx___lam__1(v___x_1525_, v___x_1526_, v_xs_1527_, v___x_21695__boxed_1545_, v___x_21696__boxed_1546_, v_val_1530_, v___x_1531_, v___x_1532_, v___x_1533_, v___x_1534_, v_ctors_1535_, v___x_1536_, v___x_1537_, v_levelParams_1538_, v_indName_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
return v_res_1547_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15(size_t v_sz_1548_, size_t v_i_1549_, lean_object* v_bs_1550_){
_start:
{
uint8_t v___x_1551_; 
v___x_1551_ = lean_usize_dec_lt(v_i_1549_, v_sz_1548_);
if (v___x_1551_ == 0)
{
return v_bs_1550_;
}
else
{
lean_object* v_v_1552_; lean_object* v___x_1553_; lean_object* v_bs_x27_1554_; lean_object* v___x_1555_; uint8_t v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; size_t v___x_1559_; size_t v___x_1560_; lean_object* v___x_1561_; 
v_v_1552_ = lean_array_uget(v_bs_1550_, v_i_1549_);
v___x_1553_ = lean_unsigned_to_nat(0u);
v_bs_x27_1554_ = lean_array_uset(v_bs_1550_, v_i_1549_, v___x_1553_);
v___x_1555_ = l_Lean_Expr_fvarId_x21(v_v_1552_);
lean_dec(v_v_1552_);
v___x_1556_ = 1;
v___x_1557_ = lean_box(v___x_1556_);
v___x_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1555_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = ((size_t)1ULL);
v___x_1560_ = lean_usize_add(v_i_1549_, v___x_1559_);
v___x_1561_ = lean_array_uset(v_bs_x27_1554_, v_i_1549_, v___x_1558_);
v_i_1549_ = v___x_1560_;
v_bs_1550_ = v___x_1561_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1548_ = stack[0].m_num;
size_t v_i_1549_ = stack[1].m_num;
lean_object* v_bs_1550_ = stack[2].m_obj;
lean_object* v_res_1563_;
v_res_1563_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15(v_sz_1548_, v_i_1549_, v_bs_1550_);
stack->m_obj
 = v_res_1563_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15___boxed(lean_object* v_sz_1564_, lean_object* v_i_1565_, lean_object* v_bs_1566_){
_start:
{
size_t v_sz_boxed_1567_; size_t v_i_boxed_1568_; lean_object* v_res_1569_; 
v_sz_boxed_1567_ = lean_unbox_usize(v_sz_1564_);
lean_dec(v_sz_1564_);
v_i_boxed_1568_ = lean_unbox_usize(v_i_1565_);
lean_dec(v_i_1565_);
v_res_1569_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15(v_sz_boxed_1567_, v_i_boxed_1568_, v_bs_1566_);
return v_res_1569_;
}
}
lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(lean_object* v_bs_1570_, lean_object* v_k_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1570_, v_k_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1577_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1577_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
v_a_1586_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1577_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1577_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_bs_1570_ = stack[0].m_obj;
lean_object* v_k_1571_ = stack[1].m_obj;
lean_object* v___y_1572_ = stack[2].m_obj;
lean_object* v___y_1573_ = stack[3].m_obj;
lean_object* v___y_1574_ = stack[4].m_obj;
lean_object* v___y_1575_ = stack[5].m_obj;
lean_object* v_res_1594_;
v_res_1594_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(v_bs_1570_, v_k_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
stack->m_obj
 = v_res_1594_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg___boxed(lean_object* v_bs_1595_, lean_object* v_k_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(v_bs_1595_, v_k_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec_ref(v_bs_1595_);
return v_res_1602_;
}
}
lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(lean_object* v_bs_1603_, lean_object* v_k_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
size_t v_sz_1610_; size_t v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v_sz_1610_ = lean_array_size(v_bs_1603_);
v___x_1611_ = ((size_t)0ULL);
v___x_1612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15(v_sz_1610_, v___x_1611_, v_bs_1603_);
v___x_1613_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(v___x_1612_, v_k_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec_ref(v___x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT void l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_bs_1603_ = stack[0].m_obj;
lean_object* v_k_1604_ = stack[1].m_obj;
lean_object* v___y_1605_ = stack[2].m_obj;
lean_object* v___y_1606_ = stack[3].m_obj;
lean_object* v___y_1607_ = stack[4].m_obj;
lean_object* v___y_1608_ = stack[5].m_obj;
lean_object* v_res_1614_;
v_res_1614_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(v_bs_1603_, v_k_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
stack->m_obj
 = v_res_1614_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg___boxed(lean_object* v_bs_1615_, lean_object* v_k_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(v_bs_1615_, v_k_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
return v_res_1622_;
}
}
lean_object* l_Lean_mkCtorIdx___lam__2(lean_object* v_numParams_1626_, lean_object* v_indName_1627_, lean_object* v___x_1628_, lean_object* v___x_1629_, uint8_t v___x_1630_, uint8_t v___x_1631_, lean_object* v_val_1632_, lean_object* v___x_1633_, lean_object* v_ctors_1634_, lean_object* v___x_1635_, lean_object* v_levelParams_1636_, lean_object* v_xs_1637_, lean_object* v_x_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___f_1656_; lean_object* v___x_1657_; 
v___x_1644_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1626_);
lean_inc_ref_n(v_xs_1637_, 3);
v___x_1645_ = l_Array_toSubarray___redArg(v_xs_1637_, v___x_1644_, v_numParams_1626_);
v___x_1646_ = l_Subarray_copy___redArg(v___x_1645_);
v___x_1647_ = lean_array_get_size(v_xs_1637_);
v___x_1648_ = l_Array_toSubarray___redArg(v_xs_1637_, v_numParams_1626_, v___x_1647_);
v___x_1649_ = l_Subarray_copy___redArg(v___x_1648_);
lean_inc(v___x_1628_);
lean_inc(v_indName_1627_);
v___x_1650_ = l_Lean_mkConst(v_indName_1627_, v___x_1628_);
v___x_1651_ = l_Lean_mkAppN(v___x_1650_, v_xs_1637_);
v___x_1652_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__2___closed__1));
v___x_1653_ = l_Lean_mkConst(v___x_1652_, v___x_1629_);
v___x_1654_ = lean_box(v___x_1630_);
v___x_1655_ = lean_box(v___x_1631_);
v___f_1656_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__1___boxed), 20, 15);
lean_closure_set(v___f_1656_, 0, v___x_1651_);
lean_closure_set(v___f_1656_, 1, v___x_1653_);
lean_closure_set(v___f_1656_, 2, v_xs_1637_);
lean_closure_set(v___f_1656_, 3, v___x_1654_);
lean_closure_set(v___f_1656_, 4, v___x_1655_);
lean_closure_set(v___f_1656_, 5, v_val_1632_);
lean_closure_set(v___f_1656_, 6, v___x_1649_);
lean_closure_set(v___f_1656_, 7, v___x_1628_);
lean_closure_set(v___f_1656_, 8, v___x_1633_);
lean_closure_set(v___f_1656_, 9, v___x_1646_);
lean_closure_set(v___f_1656_, 10, v_ctors_1634_);
lean_closure_set(v___f_1656_, 11, v___x_1644_);
lean_closure_set(v___f_1656_, 12, v___x_1635_);
lean_closure_set(v___f_1656_, 13, v_levelParams_1636_);
lean_closure_set(v___f_1656_, 14, v_indName_1627_);
v___x_1657_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(v_xs_1637_, v___f_1656_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
return v___x_1657_;
}
}
LEAN_EXPORT void l_Lean_mkCtorIdx___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_numParams_1626_ = stack[0].m_obj;
lean_object* v_indName_1627_ = stack[1].m_obj;
lean_object* v___x_1628_ = stack[2].m_obj;
lean_object* v___x_1629_ = stack[3].m_obj;
uint8_t v___x_1630_ = stack[4].m_num;
uint8_t v___x_1631_ = stack[5].m_num;
lean_object* v_val_1632_ = stack[6].m_obj;
lean_object* v___x_1633_ = stack[7].m_obj;
lean_object* v_ctors_1634_ = stack[8].m_obj;
lean_object* v___x_1635_ = stack[9].m_obj;
lean_object* v_levelParams_1636_ = stack[10].m_obj;
lean_object* v_xs_1637_ = stack[11].m_obj;
lean_object* v_x_1638_ = stack[12].m_obj;
lean_object* v___y_1639_ = stack[13].m_obj;
lean_object* v___y_1640_ = stack[14].m_obj;
lean_object* v___y_1641_ = stack[15].m_obj;
lean_object* v___y_1642_ = stack[16].m_obj;
lean_object* v_res_1658_;
v_res_1658_ = l_Lean_mkCtorIdx___lam__2(v_numParams_1626_, v_indName_1627_, v___x_1628_, v___x_1629_, v___x_1630_, v___x_1631_, v_val_1632_, v___x_1633_, v_ctors_1634_, v___x_1635_, v_levelParams_1636_, v_xs_1637_, v_x_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
stack->m_obj
 = v_res_1658_;
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2___boxed(lean_object** _args){
lean_object* v_numParams_1659_ = _args[0];
lean_object* v_indName_1660_ = _args[1];
lean_object* v___x_1661_ = _args[2];
lean_object* v___x_1662_ = _args[3];
lean_object* v___x_1663_ = _args[4];
lean_object* v___x_1664_ = _args[5];
lean_object* v_val_1665_ = _args[6];
lean_object* v___x_1666_ = _args[7];
lean_object* v_ctors_1667_ = _args[8];
lean_object* v___x_1668_ = _args[9];
lean_object* v_levelParams_1669_ = _args[10];
lean_object* v_xs_1670_ = _args[11];
lean_object* v_x_1671_ = _args[12];
lean_object* v___y_1672_ = _args[13];
lean_object* v___y_1673_ = _args[14];
lean_object* v___y_1674_ = _args[15];
lean_object* v___y_1675_ = _args[16];
lean_object* v___y_1676_ = _args[17];
_start:
{
uint8_t v___x_22371__boxed_1677_; uint8_t v___x_22372__boxed_1678_; lean_object* v_res_1679_; 
v___x_22371__boxed_1677_ = lean_unbox(v___x_1663_);
v___x_22372__boxed_1678_ = lean_unbox(v___x_1664_);
v_res_1679_ = l_Lean_mkCtorIdx___lam__2(v_numParams_1659_, v_indName_1660_, v___x_1661_, v___x_1662_, v___x_22371__boxed_1677_, v___x_22372__boxed_1678_, v_val_1665_, v___x_1666_, v_ctors_1667_, v___x_1668_, v_levelParams_1669_, v_xs_1670_, v_x_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec_ref(v_x_1671_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
if (lean_obj_tag(v_a_1680_) == 0)
{
lean_object* v___x_1682_; 
v___x_1682_ = l_List_reverse___redArg(v_a_1681_);
return v___x_1682_;
}
else
{
lean_object* v_head_1683_; lean_object* v_tail_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1693_; 
v_head_1683_ = lean_ctor_get(v_a_1680_, 0);
v_tail_1684_ = lean_ctor_get(v_a_1680_, 1);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_a_1680_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1686_ = v_a_1680_;
v_isShared_1687_ = v_isSharedCheck_1693_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_tail_1684_);
lean_inc(v_head_1683_);
lean_dec(v_a_1680_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1693_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1688_ = l_Lean_mkLevelParam(v_head_1683_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 1, v_a_1681_);
lean_ctor_set(v___x_1686_, 0, v___x_1688_);
v___x_1690_ = v___x_1686_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1688_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_a_1681_);
v___x_1690_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
v_a_1680_ = v_tail_1684_;
v_a_1681_ = v___x_1690_;
goto _start;
}
}
}
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg(lean_object* v_ref_1694_, lean_object* v_msg_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v_toCold_1701_; lean_object* v_currRecDepth_1702_; lean_object* v_ref_1703_; uint16_t v_optionFlags_1704_; uint8_t v_suppressElabErrors_1705_; uint8_t v_isRecordingDeps_1706_; lean_object* v_ref_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v_toCold_1701_ = lean_ctor_get(v___y_1698_, 0);
v_currRecDepth_1702_ = lean_ctor_get(v___y_1698_, 1);
v_ref_1703_ = lean_ctor_get(v___y_1698_, 2);
v_optionFlags_1704_ = lean_ctor_get_uint16(v___y_1698_, sizeof(void*)*3);
v_suppressElabErrors_1705_ = lean_ctor_get_uint8(v___y_1698_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1706_ = lean_ctor_get_uint8(v___y_1698_, sizeof(void*)*3 + 3);
v_ref_1707_ = l_Lean_replaceRef(v_ref_1694_, v_ref_1703_);
lean_inc(v_currRecDepth_1702_);
lean_inc_ref(v_toCold_1701_);
v___x_1708_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1708_, 0, v_toCold_1701_);
lean_ctor_set(v___x_1708_, 1, v_currRecDepth_1702_);
lean_ctor_set(v___x_1708_, 2, v_ref_1707_);
lean_ctor_set_uint16(v___x_1708_, sizeof(void*)*3, v_optionFlags_1704_);
lean_ctor_set_uint8(v___x_1708_, sizeof(void*)*3 + 2, v_suppressElabErrors_1705_);
lean_ctor_set_uint8(v___x_1708_, sizeof(void*)*3 + 3, v_isRecordingDeps_1706_);
v___x_1709_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_1695_, v___y_1696_, v___y_1697_, v___x_1708_, v___y_1699_);
lean_dec_ref_known(v___x_1708_, 3);
return v___x_1709_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1694_ = stack[0].m_obj;
lean_object* v_msg_1695_ = stack[1].m_obj;
lean_object* v___y_1696_ = stack[2].m_obj;
lean_object* v___y_1697_ = stack[3].m_obj;
lean_object* v___y_1698_ = stack[4].m_obj;
lean_object* v___y_1699_ = stack[5].m_obj;
lean_object* v_res_1710_;
v_res_1710_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg(v_ref_1694_, v_msg_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
stack->m_obj
 = v_res_1710_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg___boxed(lean_object* v_ref_1711_, lean_object* v_msg_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg(v_ref_1711_, v_msg_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v_ref_1711_);
return v_res_1718_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1);
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
return v___x_1720_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__1(void){
_start:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1721_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1722_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0);
v___x_1723_ = lean_unsigned_to_nat(0u);
v___x_1724_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
lean_ctor_set(v___x_1724_, 2, v___x_1723_);
lean_ctor_set(v___x_1724_, 3, v___x_1723_);
lean_ctor_set(v___x_1724_, 4, v___x_1722_);
lean_ctor_set(v___x_1724_, 5, v___x_1722_);
lean_ctor_set(v___x_1724_, 6, v___x_1722_);
lean_ctor_set(v___x_1724_, 7, v___x_1722_);
lean_ctor_set(v___x_1724_, 8, v___x_1722_);
lean_ctor_set(v___x_1724_, 9, v___x_1722_);
lean_ctor_set(v___x_1724_, 10, v___x_1722_);
lean_ctor_set(v___x_1724_, 11, v___x_1721_);
return v___x_1724_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = lean_unsigned_to_nat(32u);
v___x_1726_ = lean_mk_empty_array_with_capacity(v___x_1725_);
v___x_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
return v___x_1727_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__3(void){
_start:
{
size_t v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1728_ = ((size_t)5ULL);
v___x_1729_ = lean_unsigned_to_nat(0u);
v___x_1730_ = lean_unsigned_to_nat(32u);
v___x_1731_ = lean_mk_empty_array_with_capacity(v___x_1730_);
v___x_1732_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__2);
v___x_1733_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
lean_ctor_set(v___x_1733_, 1, v___x_1731_);
lean_ctor_set(v___x_1733_, 2, v___x_1729_);
lean_ctor_set(v___x_1733_, 3, v___x_1729_);
lean_ctor_set_usize(v___x_1733_, 4, v___x_1728_);
return v___x_1733_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__4(void){
_start:
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1734_ = lean_box(1);
v___x_1735_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__3);
v___x_1736_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0);
v___x_1737_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
lean_ctor_set(v___x_1737_, 1, v___x_1735_);
lean_ctor_set(v___x_1737_, 2, v___x_1734_);
return v___x_1737_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__5));
v___x_1740_ = l_Lean_stringToMessageData(v___x_1739_);
return v___x_1740_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__8(void){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__7));
v___x_1743_ = l_Lean_stringToMessageData(v___x_1742_);
return v___x_1743_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__10(void){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__9));
v___x_1746_ = l_Lean_stringToMessageData(v___x_1745_);
return v___x_1746_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__12(void){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__11));
v___x_1749_ = l_Lean_stringToMessageData(v___x_1748_);
return v___x_1749_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__14(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__13));
v___x_1752_ = l_Lean_stringToMessageData(v___x_1751_);
return v___x_1752_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__15));
v___x_1755_ = l_Lean_stringToMessageData(v___x_1754_);
return v___x_1755_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18(void){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__17));
v___x_1758_ = l_Lean_stringToMessageData(v___x_1757_);
return v___x_1758_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__20(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__19));
v___x_1761_ = l_Lean_stringToMessageData(v___x_1760_);
return v___x_1761_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__22(void){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__21));
v___x_1764_ = l_Lean_stringToMessageData(v___x_1763_);
return v___x_1764_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__24(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__23));
v___x_1767_ = l_Lean_stringToMessageData(v___x_1766_);
return v___x_1767_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__26(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__25));
v___x_1770_ = l_Lean_stringToMessageData(v___x_1769_);
return v___x_1770_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg(lean_object* v_msg_1771_, lean_object* v_declHint_1772_, lean_object* v___y_1773_){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v_env_1777_; uint8_t v___x_1778_; 
v___x_1775_ = lean_box(0);
v___x_1776_ = lean_st_ref_get(v___y_1773_);
v_env_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc_ref(v_env_1777_);
lean_dec(v___x_1776_);
v___x_1778_ = l_Lean_Name_isAnonymous(v_declHint_1772_);
if (v___x_1778_ == 0)
{
uint8_t v_isExporting_1779_; 
v_isExporting_1779_ = lean_ctor_get_uint8(v_env_1777_, sizeof(void*)*13);
if (v_isExporting_1779_ == 0)
{
lean_object* v___x_1780_; 
lean_dec_ref(v_env_1777_);
lean_dec(v_declHint_1772_);
v___x_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1780_, 0, v_msg_1771_);
return v___x_1780_;
}
else
{
lean_object* v___x_1781_; uint8_t v___x_1782_; 
lean_inc_ref(v_env_1777_);
v___x_1781_ = l_Lean_Environment_setExporting(v_env_1777_, v___x_1778_);
lean_inc(v_declHint_1772_);
lean_inc_ref(v___x_1781_);
v___x_1782_ = l_Lean_Environment_contains(v___x_1781_, v_declHint_1772_, v_isExporting_1779_);
if (v___x_1782_ == 0)
{
lean_object* v___x_1783_; 
lean_dec_ref(v___x_1781_);
lean_dec_ref(v_env_1777_);
lean_dec(v_declHint_1772_);
v___x_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1783_, 0, v_msg_1771_);
return v___x_1783_;
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v_c_1789_; lean_object* v___x_1790_; 
v___x_1784_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__1);
v___x_1785_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__4);
v___x_1786_ = l_Lean_Options_empty;
v___x_1787_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1781_);
lean_ctor_set(v___x_1787_, 1, v___x_1784_);
lean_ctor_set(v___x_1787_, 2, v___x_1785_);
lean_ctor_set(v___x_1787_, 3, v___x_1786_);
lean_inc(v_declHint_1772_);
v___x_1788_ = l_Lean_MessageData_ofConstName(v_declHint_1772_, v___x_1778_);
v_c_1789_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1789_, 0, v___x_1787_);
lean_ctor_set(v_c_1789_, 1, v___x_1788_);
v___x_1790_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1777_, v_declHint_1772_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_dec_ref(v_env_1777_);
lean_dec(v_declHint_1772_);
v___x_1791_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6);
v___x_1792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1791_);
lean_ctor_set(v___x_1792_, 1, v_c_1789_);
v___x_1793_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__8);
v___x_1794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1792_);
lean_ctor_set(v___x_1794_, 1, v___x_1793_);
v___x_1795_ = l_Lean_MessageData_note(v___x_1794_);
v___x_1796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1796_, 0, v_msg_1771_);
lean_ctor_set(v___x_1796_, 1, v___x_1795_);
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
return v___x_1797_;
}
else
{
lean_object* v_val_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1854_; 
v_val_1798_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1800_ = v___x_1790_;
v_isShared_1801_ = v_isSharedCheck_1854_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_val_1798_);
lean_dec(v___x_1790_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1854_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v_modules_1803_; lean_object* v_moduleNames_1804_; lean_object* v_mod_1805_; uint8_t v___y_1807_; uint8_t v___x_1837_; 
v___x_1802_ = l_Lean_Environment_header(v_env_1777_);
lean_dec_ref(v_env_1777_);
v_modules_1803_ = lean_ctor_get(v___x_1802_, 3);
lean_inc_ref(v_modules_1803_);
v_moduleNames_1804_ = lean_ctor_get(v___x_1802_, 4);
lean_inc_ref(v_moduleNames_1804_);
lean_dec_ref(v___x_1802_);
v_mod_1805_ = lean_array_get(v___x_1775_, v_moduleNames_1804_, v_val_1798_);
lean_dec_ref(v_moduleNames_1804_);
v___x_1837_ = l_Lean_isPrivateName(v_declHint_1772_);
lean_dec(v_declHint_1772_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1838_ = lean_array_get_size(v_modules_1803_);
v___x_1839_ = lean_nat_dec_lt(v_val_1798_, v___x_1838_);
if (v___x_1839_ == 0)
{
lean_dec_ref(v_modules_1803_);
lean_dec(v_val_1798_);
v___y_1807_ = v___x_1837_;
goto v___jp_1806_;
}
else
{
lean_object* v___x_1840_; lean_object* v_toImport_1841_; uint8_t v_isExported_1842_; 
v___x_1840_ = lean_array_fget(v_modules_1803_, v_val_1798_);
lean_dec(v_val_1798_);
lean_dec_ref(v_modules_1803_);
v_toImport_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc_ref(v_toImport_1841_);
lean_dec(v___x_1840_);
v_isExported_1842_ = lean_ctor_get_uint8(v_toImport_1841_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1841_);
v___y_1807_ = v_isExported_1842_;
goto v___jp_1806_;
}
}
else
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_dec_ref(v_modules_1803_);
lean_del_object(v___x_1800_);
lean_dec(v_val_1798_);
v___x_1843_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6);
v___x_1844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
lean_ctor_set(v___x_1844_, 1, v_c_1789_);
v___x_1845_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__24);
v___x_1846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1844_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = l_Lean_MessageData_ofName(v_mod_1805_);
v___x_1848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1846_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__26, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__26_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__26);
v___x_1850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1848_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = l_Lean_MessageData_note(v___x_1850_);
v___x_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1852_, 0, v_msg_1771_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
return v___x_1853_;
}
v___jp_1806_:
{
if (v___y_1807_ == 0)
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1808_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__10);
v___x_1809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
lean_ctor_set(v___x_1809_, 1, v_c_1789_);
v___x_1810_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__12);
v___x_1811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1809_);
lean_ctor_set(v___x_1811_, 1, v___x_1810_);
v___x_1812_ = l_Lean_MessageData_ofName(v_mod_1805_);
v___x_1813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1811_);
lean_ctor_set(v___x_1813_, 1, v___x_1812_);
v___x_1814_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__14);
v___x_1815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1813_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = l_Lean_MessageData_note(v___x_1815_);
v___x_1817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1817_, 0, v_msg_1771_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set_tag(v___x_1800_, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1817_);
v___x_1819_ = v___x_1800_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
else
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1821_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16);
v___x_1822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
lean_ctor_set(v___x_1822_, 1, v_c_1789_);
v___x_1823_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18);
v___x_1824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1822_);
lean_ctor_set(v___x_1824_, 1, v___x_1823_);
v___x_1825_ = l_Lean_MessageData_ofName(v_mod_1805_);
lean_inc_ref(v___x_1825_);
v___x_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1824_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__20);
v___x_1828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1826_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
lean_ctor_set(v___x_1829_, 1, v___x_1825_);
v___x_1830_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__22);
v___x_1831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1829_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = l_Lean_MessageData_note(v___x_1831_);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v_msg_1771_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set_tag(v___x_1800_, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1833_);
v___x_1835_ = v___x_1800_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
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
lean_object* v___x_1855_; 
lean_dec_ref(v_env_1777_);
lean_dec(v_declHint_1772_);
v___x_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1855_, 0, v_msg_1771_);
return v___x_1855_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1771_ = stack[0].m_obj;
lean_object* v_declHint_1772_ = stack[1].m_obj;
lean_object* v___y_1773_ = stack[2].m_obj;
lean_object* v_res_1856_;
v_res_1856_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg(v_msg_1771_, v_declHint_1772_, v___y_1773_);
stack->m_obj
 = v_res_1856_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___boxed(lean_object* v_msg_1857_, lean_object* v_declHint_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg(v_msg_1857_, v_declHint_1858_, v___y_1859_);
lean_dec(v___y_1859_);
return v_res_1861_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22(lean_object* v_msg_1862_, lean_object* v_declHint_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___x_1869_; lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1879_; 
v___x_1869_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg(v_msg_1862_, v_declHint_1863_, v___y_1867_);
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1872_ = v___x_1869_;
v_isShared_1873_ = v_isSharedCheck_1879_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1869_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1879_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1877_; 
v___x_1874_ = l_Lean_unknownIdentifierMessageTag;
v___x_1875_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v_a_1870_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1875_);
v___x_1877_ = v___x_1872_;
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
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1862_ = stack[0].m_obj;
lean_object* v_declHint_1863_ = stack[1].m_obj;
lean_object* v___y_1864_ = stack[2].m_obj;
lean_object* v___y_1865_ = stack[3].m_obj;
lean_object* v___y_1866_ = stack[4].m_obj;
lean_object* v___y_1867_ = stack[5].m_obj;
lean_object* v_res_1880_;
v_res_1880_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22(v_msg_1862_, v_declHint_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
stack->m_obj
 = v_res_1880_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22___boxed(lean_object* v_msg_1881_, lean_object* v_declHint_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22(v_msg_1881_, v_declHint_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
return v_res_1888_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg(lean_object* v_ref_1889_, lean_object* v_msg_1890_, lean_object* v_declHint_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v___x_1897_; lean_object* v_a_1898_; lean_object* v___x_1899_; 
v___x_1897_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22(v_msg_1890_, v_declHint_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref(v___x_1897_);
v___x_1899_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg(v_ref_1889_, v_a_1898_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
return v___x_1899_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1889_ = stack[0].m_obj;
lean_object* v_msg_1890_ = stack[1].m_obj;
lean_object* v_declHint_1891_ = stack[2].m_obj;
lean_object* v___y_1892_ = stack[3].m_obj;
lean_object* v___y_1893_ = stack[4].m_obj;
lean_object* v___y_1894_ = stack[5].m_obj;
lean_object* v___y_1895_ = stack[6].m_obj;
lean_object* v_res_1900_;
v_res_1900_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg(v_ref_1889_, v_msg_1890_, v_declHint_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
stack->m_obj
 = v_res_1900_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg___boxed(lean_object* v_ref_1901_, lean_object* v_msg_1902_, lean_object* v_declHint_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg(v_ref_1901_, v_msg_1902_, v_declHint_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v_ref_1901_);
return v_res_1909_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1911_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0));
v___x_1912_ = l_Lean_stringToMessageData(v___x_1911_);
return v___x_1912_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(lean_object* v_ref_1913_, lean_object* v_constName_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v___x_1920_; uint8_t v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1920_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1);
v___x_1921_ = 0;
lean_inc(v_constName_1914_);
v___x_1922_ = l_Lean_MessageData_ofConstName(v_constName_1914_, v___x_1921_);
v___x_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1920_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg(v_ref_1913_, v___x_1925_, v_constName_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
return v___x_1926_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1913_ = stack[0].m_obj;
lean_object* v_constName_1914_ = stack[1].m_obj;
lean_object* v___y_1915_ = stack[2].m_obj;
lean_object* v___y_1916_ = stack[3].m_obj;
lean_object* v___y_1917_ = stack[4].m_obj;
lean_object* v___y_1918_ = stack[5].m_obj;
lean_object* v_res_1927_;
v_res_1927_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1913_, v_constName_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
stack->m_obj
 = v_res_1927_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1928_, lean_object* v_constName_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1928_, v_constName_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v_ref_1928_);
return v_res_1935_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(lean_object* v_constName_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_ref_1942_; lean_object* v___x_1943_; 
v_ref_1942_ = lean_ctor_get(v___y_1939_, 2);
v___x_1943_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1942_, v_constName_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
return v___x_1943_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1936_ = stack[0].m_obj;
lean_object* v___y_1937_ = stack[1].m_obj;
lean_object* v___y_1938_ = stack[2].m_obj;
lean_object* v___y_1939_ = stack[3].m_obj;
lean_object* v___y_1940_ = stack[4].m_obj;
lean_object* v_res_1944_;
v_res_1944_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
stack->m_obj
 = v_res_1944_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg___boxed(lean_object* v_constName_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
return v_res_1951_;
}
}
lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(lean_object* v_constName_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v___x_1958_; lean_object* v_env_1959_; uint8_t v___x_1960_; lean_object* v___x_1961_; 
v___x_1958_ = lean_st_ref_get(v___y_1956_);
v_env_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc_ref(v_env_1959_);
lean_dec(v___x_1958_);
v___x_1960_ = 0;
lean_inc(v_constName_1952_);
v___x_1961_ = l_Lean_Environment_find_x3f(v_env_1959_, v_constName_1952_, v___x_1960_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
return v___x_1962_;
}
else
{
lean_object* v_val_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec(v_constName_1952_);
v_val_1963_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1961_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_val_1963_);
lean_dec(v___x_1961_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
lean_ctor_set_tag(v___x_1965_, 0);
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_val_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1952_ = stack[0].m_obj;
lean_object* v___y_1953_ = stack[1].m_obj;
lean_object* v___y_1954_ = stack[2].m_obj;
lean_object* v___y_1955_ = stack[3].m_obj;
lean_object* v___y_1956_ = stack[4].m_obj;
lean_object* v_res_1971_;
v_res_1971_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_constName_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
stack->m_obj
 = v_res_1971_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2___boxed(lean_object* v_constName_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_constName_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
return v_res_1978_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1981_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6));
v___x_1982_ = lean_unsigned_to_nat(62u);
v___x_1983_ = lean_unsigned_to_nat(83u);
v___x_1984_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__3___closed__1));
v___x_1985_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__3___closed__0));
v___x_1986_ = l_mkPanicMessageWithDecl(v___x_1985_, v___x_1984_, v___x_1983_, v___x_1982_, v___x_1981_);
return v___x_1986_;
}
}
lean_object* l_Lean_mkCtorIdx___lam__3(lean_object* v_indName_1987_, uint8_t v___x_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1994_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1991_);
v___x_1995_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_genCtorIdx;
v___x_1996_ = l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(v___x_1994_, v___x_1995_);
lean_dec_ref(v___x_1994_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
lean_dec(v_indName_1987_);
v___x_1997_ = lean_box(0);
v___x_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
return v___x_1998_;
}
else
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2085_; 
lean_inc(v_indName_1987_);
v___x_1999_ = l_Lean_mkCtorIdxName(v_indName_1987_);
lean_inc(v___x_1999_);
v___x_2000_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v___x_1999_, v___x_1996_, v___y_1992_);
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2003_ = v___x_2000_;
v_isShared_2004_ = v_isSharedCheck_2085_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2085_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
uint8_t v___x_2005_; 
v___x_2005_ = lean_unbox(v_a_2001_);
lean_dec(v_a_2001_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; 
lean_del_object(v___x_2003_);
lean_inc(v_indName_1987_);
v___x_2006_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_indName_1987_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_2006_, 1);
if (lean_obj_tag(v_a_2007_) == 5)
{
lean_object* v_val_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2070_; 
v_val_2008_ = lean_ctor_get(v_a_2007_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v_a_2007_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2010_ = v_a_2007_;
v_isShared_2011_ = v_isSharedCheck_2070_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_val_2008_);
lean_dec(v_a_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2070_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v_toConstantVal_2012_; lean_object* v_numParams_2013_; lean_object* v_numIndices_2014_; lean_object* v_ctors_2015_; lean_object* v_levelParams_2016_; lean_object* v_type_2017_; lean_object* v___x_2018_; 
v_toConstantVal_2012_ = lean_ctor_get(v_val_2008_, 0);
v_numParams_2013_ = lean_ctor_get(v_val_2008_, 1);
lean_inc(v_numParams_2013_);
v_numIndices_2014_ = lean_ctor_get(v_val_2008_, 2);
lean_inc(v_numIndices_2014_);
v_ctors_2015_ = lean_ctor_get(v_val_2008_, 4);
lean_inc(v_ctors_2015_);
v_levelParams_2016_ = lean_ctor_get(v_toConstantVal_2012_, 1);
lean_inc(v_levelParams_2016_);
v_type_2017_ = lean_ctor_get(v_toConstantVal_2012_, 2);
lean_inc_ref_n(v_type_2017_, 2);
v___x_2018_ = l_Lean_Meta_isPropFormerType(v_type_2017_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2061_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2021_ = v___x_2018_;
v_isShared_2022_ = v_isSharedCheck_2061_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2018_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2061_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
uint8_t v___x_2023_; 
v___x_2023_ = lean_unbox(v_a_2019_);
lean_dec(v_a_2019_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
lean_del_object(v___x_2021_);
lean_inc(v_indName_1987_);
v___x_2024_ = l_Lean_mkCasesOnName(v_indName_1987_);
lean_inc(v___x_2024_);
v___x_2025_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v___x_2024_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2048_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2028_ = v___x_2025_;
v_isShared_2029_ = v_isSharedCheck_2048_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2025_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2048_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v___x_2030_ = l_List_lengthTR___redArg(v_levelParams_2016_);
v___x_2031_ = l_Lean_ConstantInfo_levelParams(v_a_2026_);
lean_dec(v_a_2026_);
v___x_2032_ = l_List_lengthTR___redArg(v___x_2031_);
lean_dec(v___x_2031_);
v___x_2033_ = lean_nat_dec_lt(v___x_2030_, v___x_2032_);
lean_dec(v___x_2032_);
lean_dec(v___x_2030_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; lean_object* v___x_2036_; 
lean_dec(v___x_2024_);
lean_dec_ref(v_type_2017_);
lean_dec(v_levelParams_2016_);
lean_dec(v_ctors_2015_);
lean_dec(v_numIndices_2014_);
lean_dec(v_numParams_2013_);
lean_del_object(v___x_2010_);
lean_dec_ref(v_val_2008_);
lean_dec(v___x_1999_);
lean_dec(v_indName_1987_);
v___x_2034_ = lean_box(0);
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v___x_2034_);
v___x_2036_ = v___x_2028_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___f_2042_; lean_object* v___x_2043_; lean_object* v___x_2045_; 
lean_del_object(v___x_2028_);
v___x_2038_ = lean_box(0);
lean_inc(v_levelParams_2016_);
v___x_2039_ = l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(v_levelParams_2016_, v___x_2038_);
v___x_2040_ = lean_box(v___x_1988_);
v___x_2041_ = lean_box(v___x_1996_);
lean_inc(v_numParams_2013_);
v___f_2042_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__2___boxed), 18, 11);
lean_closure_set(v___f_2042_, 0, v_numParams_2013_);
lean_closure_set(v___f_2042_, 1, v_indName_1987_);
lean_closure_set(v___f_2042_, 2, v___x_2039_);
lean_closure_set(v___f_2042_, 3, v___x_2038_);
lean_closure_set(v___f_2042_, 4, v___x_2040_);
lean_closure_set(v___f_2042_, 5, v___x_2041_);
lean_closure_set(v___f_2042_, 6, v_val_2008_);
lean_closure_set(v___f_2042_, 7, v___x_2024_);
lean_closure_set(v___f_2042_, 8, v_ctors_2015_);
lean_closure_set(v___f_2042_, 9, v___x_1999_);
lean_closure_set(v___f_2042_, 10, v_levelParams_2016_);
v___x_2043_ = lean_nat_add(v_numParams_2013_, v_numIndices_2014_);
lean_dec(v_numIndices_2014_);
lean_dec(v_numParams_2013_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set_tag(v___x_2010_, 1);
lean_ctor_set(v___x_2010_, 0, v___x_2043_);
v___x_2045_ = v___x_2010_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_2017_, v___x_2045_, v___f_2042_, v___x_1988_, v___x_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
return v___x_2046_;
}
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec(v___x_2024_);
lean_dec_ref(v_type_2017_);
lean_dec(v_levelParams_2016_);
lean_dec(v_ctors_2015_);
lean_dec(v_numIndices_2014_);
lean_dec(v_numParams_2013_);
lean_del_object(v___x_2010_);
lean_dec_ref(v_val_2008_);
lean_dec(v___x_1999_);
lean_dec(v_indName_1987_);
v_a_2049_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2025_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2025_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2059_; 
lean_dec_ref(v_type_2017_);
lean_dec(v_levelParams_2016_);
lean_dec(v_ctors_2015_);
lean_dec(v_numIndices_2014_);
lean_dec(v_numParams_2013_);
lean_del_object(v___x_2010_);
lean_dec_ref(v_val_2008_);
lean_dec(v___x_1999_);
lean_dec(v_indName_1987_);
v___x_2057_ = lean_box(0);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2057_);
v___x_2059_ = v___x_2021_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec_ref(v_type_2017_);
lean_dec(v_levelParams_2016_);
lean_dec(v_ctors_2015_);
lean_dec(v_numIndices_2014_);
lean_dec(v_numParams_2013_);
lean_del_object(v___x_2010_);
lean_dec_ref(v_val_2008_);
lean_dec(v___x_1999_);
lean_dec(v_indName_1987_);
v_a_2062_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2018_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2018_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
}
else
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
lean_dec(v_a_2007_);
lean_dec(v___x_1999_);
lean_dec(v_indName_1987_);
v___x_2071_ = lean_obj_once(&l_Lean_mkCtorIdx___lam__3___closed__2, &l_Lean_mkCtorIdx___lam__3___closed__2_once, _init_l_Lean_mkCtorIdx___lam__3___closed__2);
v___x_2072_ = l_panic___at___00Lean_mkCtorIdx_spec__11(v___x_2071_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
return v___x_2072_;
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec(v___x_1999_);
lean_dec(v_indName_1987_);
v_a_2073_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2006_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2006_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
lean_dec(v___x_1999_);
lean_dec(v_indName_1987_);
v___x_2081_ = lean_box(0);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2081_);
v___x_2083_ = v___x_2003_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkCtorIdx___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_indName_1987_ = stack[0].m_obj;
uint8_t v___x_1988_ = stack[1].m_num;
lean_object* v___y_1989_ = stack[2].m_obj;
lean_object* v___y_1990_ = stack[3].m_obj;
lean_object* v___y_1991_ = stack[4].m_obj;
lean_object* v___y_1992_ = stack[5].m_obj;
lean_object* v_res_2086_;
v_res_2086_ = l_Lean_mkCtorIdx___lam__3(v_indName_1987_, v___x_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
stack->m_obj
 = v_res_2086_;
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3___boxed(lean_object* v_indName_2087_, lean_object* v___x_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
uint8_t v___x_23277__boxed_2094_; lean_object* v_res_2095_; 
v___x_23277__boxed_2094_ = lean_unbox(v___x_2088_);
v_res_2095_ = l_Lean_mkCtorIdx___lam__3(v_indName_2087_, v___x_23277__boxed_2094_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__4(lean_object* v___x_2096_, lean_object* v_e_2097_){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = l_Lean_indentD(v_e_2097_);
v___x_2099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2096_);
lean_ctor_set(v___x_2099_, 1, v___x_2098_);
return v___x_2099_;
}
}
lean_object* l_Lean_mkCtorIdx___lam__5(lean_object* v___f_2100_, lean_object* v___f_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Lean_Meta_mapErrorImp___redArg(v___f_2100_, v___f_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2107_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2107_);
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
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
v_a_2116_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2107_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2107_);
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
}
LEAN_EXPORT void l_Lean_mkCtorIdx___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2100_ = stack[0].m_obj;
lean_object* v___f_2101_ = stack[1].m_obj;
lean_object* v___y_2102_ = stack[2].m_obj;
lean_object* v___y_2103_ = stack[3].m_obj;
lean_object* v___y_2104_ = stack[4].m_obj;
lean_object* v___y_2105_ = stack[5].m_obj;
lean_object* v_res_2124_;
v_res_2124_ = l_Lean_mkCtorIdx___lam__5(v___f_2100_, v___f_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
stack->m_obj
 = v_res_2124_;
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5___boxed(lean_object* v___f_2125_, lean_object* v___f_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Lean_mkCtorIdx___lam__5(v___f_2125_, v___f_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
return v_res_2132_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___closed__1(void){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = ((lean_object*)(l_Lean_mkCtorIdx___closed__0));
v___x_2135_ = l_Lean_stringToMessageData(v___x_2134_);
return v___x_2135_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___closed__3(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = ((lean_object*)(l_Lean_mkCtorIdx___closed__2));
v___x_2138_ = l_Lean_stringToMessageData(v___x_2137_);
return v___x_2138_;
}
}
lean_object* l_Lean_mkCtorIdx(lean_object* v_indName_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_){
_start:
{
lean_object* v___x_2145_; uint8_t v___x_2146_; lean_object* v___x_2147_; lean_object* v___f_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___f_2153_; lean_object* v___f_2154_; uint8_t v___x_2155_; 
v___x_2145_ = lean_obj_once(&l_Lean_mkCtorIdx___closed__1, &l_Lean_mkCtorIdx___closed__1_once, _init_l_Lean_mkCtorIdx___closed__1);
v___x_2146_ = 0;
v___x_2147_ = lean_box(v___x_2146_);
lean_inc_n(v_indName_2139_, 2);
v___f_2148_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__3___boxed), 7, 2);
lean_closure_set(v___f_2148_, 0, v_indName_2139_);
lean_closure_set(v___f_2148_, 1, v___x_2147_);
v___x_2149_ = l_Lean_MessageData_ofConstName(v_indName_2139_, v___x_2146_);
v___x_2150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2145_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = lean_obj_once(&l_Lean_mkCtorIdx___closed__3, &l_Lean_mkCtorIdx___closed__3_once, _init_l_Lean_mkCtorIdx___closed__3);
v___x_2152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2150_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___f_2153_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__4), 2, 1);
lean_closure_set(v___f_2153_, 0, v___x_2152_);
v___f_2154_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__5___boxed), 7, 2);
lean_closure_set(v___f_2154_, 0, v___f_2148_);
lean_closure_set(v___f_2154_, 1, v___f_2153_);
v___x_2155_ = l_Lean_isPrivateName(v_indName_2139_);
lean_dec(v_indName_2139_);
if (v___x_2155_ == 0)
{
uint8_t v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = 1;
v___x_2157_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(v___f_2154_, v___x_2156_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
return v___x_2157_;
}
else
{
lean_object* v___x_2158_; 
v___x_2158_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(v___f_2154_, v___x_2146_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
return v___x_2158_;
}
}
}
LEAN_EXPORT void l_Lean_mkCtorIdx_0interp(lean_interpreter_value* stack)
{
lean_object* v_indName_2139_ = stack[0].m_obj;
lean_object* v_a_2140_ = stack[1].m_obj;
lean_object* v_a_2141_ = stack[2].m_obj;
lean_object* v_a_2142_ = stack[3].m_obj;
lean_object* v_a_2143_ = stack[4].m_obj;
lean_object* v_res_2159_;
v_res_2159_ = l_Lean_mkCtorIdx(v_indName_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
stack->m_obj
 = v_res_2159_;
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___boxed(lean_object* v_indName_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Lean_mkCtorIdx(v_indName_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
lean_dec(v_a_2164_);
lean_dec_ref(v_a_2163_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
return v_res_2166_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(uint8_t v___x_2167_, lean_object* v___x_2168_, lean_object* v_as_2169_, lean_object* v_as_x27_2170_, lean_object* v_b_2171_, lean_object* v_a_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_2167_, v___x_2168_, v_as_x27_2170_, v_b_2171_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
return v___x_2178_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2167_ = stack[0].m_num;
lean_object* v___x_2168_ = stack[1].m_obj;
lean_object* v_as_2169_ = stack[2].m_obj;
lean_object* v_as_x27_2170_ = stack[3].m_obj;
lean_object* v_b_2171_ = stack[4].m_obj;
lean_object* v___y_2173_ = stack[6].m_obj;
lean_object* v___y_2174_ = stack[7].m_obj;
lean_object* v___y_2175_ = stack[8].m_obj;
lean_object* v___y_2176_ = stack[9].m_obj;
lean_object* v_res_2179_;
v_res_2179_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(v___x_2167_, v___x_2168_, v_as_2169_, v_as_x27_2170_, v_b_2171_, lean_box(0), v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
stack->m_obj
 = v_res_2179_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___boxed(lean_object* v___x_2180_, lean_object* v___x_2181_, lean_object* v_as_2182_, lean_object* v_as_x27_2183_, lean_object* v_b_2184_, lean_object* v_a_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
uint8_t v___x_23748__boxed_2191_; lean_object* v_res_2192_; 
v___x_23748__boxed_2191_ = lean_unbox(v___x_2180_);
v_res_2192_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(v___x_23748__boxed_2191_, v___x_2181_, v_as_2182_, v_as_x27_2183_, v_b_2184_, v_a_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v_as_x27_2183_);
lean_dec(v_as_2182_);
lean_dec_ref(v___x_2181_);
return v_res_2192_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10(lean_object* v_00_u03b1_2193_, lean_object* v_name_2194_, uint8_t v_bi_2195_, lean_object* v_type_2196_, lean_object* v_k_2197_, uint8_t v_kind_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_2194_, v_bi_2195_, v_type_2196_, v_k_2197_, v_kind_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
return v___x_2204_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2194_ = stack[1].m_obj;
uint8_t v_bi_2195_ = stack[2].m_num;
lean_object* v_type_2196_ = stack[3].m_obj;
lean_object* v_k_2197_ = stack[4].m_obj;
uint8_t v_kind_2198_ = stack[5].m_num;
lean_object* v___y_2199_ = stack[6].m_obj;
lean_object* v___y_2200_ = stack[7].m_obj;
lean_object* v___y_2201_ = stack[8].m_obj;
lean_object* v___y_2202_ = stack[9].m_obj;
lean_object* v_res_2205_;
v_res_2205_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10(lean_box(0), v_name_2194_, v_bi_2195_, v_type_2196_, v_k_2197_, v_kind_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
stack->m_obj
 = v_res_2205_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2206_, lean_object* v_name_2207_, lean_object* v_bi_2208_, lean_object* v_type_2209_, lean_object* v_k_2210_, lean_object* v_kind_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
uint8_t v_bi_boxed_2217_; uint8_t v_kind_boxed_2218_; lean_object* v_res_2219_; 
v_bi_boxed_2217_ = lean_unbox(v_bi_2208_);
v_kind_boxed_2218_ = lean_unbox(v_kind_2211_);
v_res_2219_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10(v_00_u03b1_2206_, v_name_2207_, v_bi_boxed_2217_, v_type_2209_, v_k_2210_, v_kind_boxed_2218_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
return v_res_2219_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7(lean_object* v_00_u03b1_2220_, lean_object* v_name_2221_, lean_object* v_type_2222_, lean_object* v_k_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v_name_2221_, v_type_2222_, v_k_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
return v___x_2229_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2221_ = stack[1].m_obj;
lean_object* v_type_2222_ = stack[2].m_obj;
lean_object* v_k_2223_ = stack[3].m_obj;
lean_object* v___y_2224_ = stack[4].m_obj;
lean_object* v___y_2225_ = stack[5].m_obj;
lean_object* v___y_2226_ = stack[6].m_obj;
lean_object* v___y_2227_ = stack[7].m_obj;
lean_object* v_res_2230_;
v_res_2230_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7(lean_box(0), v_name_2221_, v_type_2222_, v_k_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
stack->m_obj
 = v_res_2230_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___boxed(lean_object* v_00_u03b1_2231_, lean_object* v_name_2232_, lean_object* v_type_2233_, lean_object* v_k_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7(v_00_u03b1_2231_, v_name_2232_, v_type_2233_, v_k_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
return v_res_2240_;
}
}
lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13(lean_object* v_env_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(v_env_2241_, v___y_2243_, v___y_2245_);
return v___x_2247_;
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_2241_ = stack[0].m_obj;
lean_object* v___y_2242_ = stack[1].m_obj;
lean_object* v___y_2243_ = stack[2].m_obj;
lean_object* v___y_2244_ = stack[3].m_obj;
lean_object* v___y_2245_ = stack[4].m_obj;
lean_object* v_res_2248_;
v_res_2248_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13(v_env_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
stack->m_obj
 = v_res_2248_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___boxed(lean_object* v_env_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13(v_env_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
return v_res_2255_;
}
}
lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16(lean_object* v_00_u03b1_2256_, lean_object* v_bs_2257_, lean_object* v_k_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(v_bs_2257_, v_k_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
return v___x_2264_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_bs_2257_ = stack[1].m_obj;
lean_object* v_k_2258_ = stack[2].m_obj;
lean_object* v___y_2259_ = stack[3].m_obj;
lean_object* v___y_2260_ = stack[4].m_obj;
lean_object* v___y_2261_ = stack[5].m_obj;
lean_object* v___y_2262_ = stack[6].m_obj;
lean_object* v_res_2265_;
v_res_2265_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16(lean_box(0), v_bs_2257_, v_k_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
stack->m_obj
 = v_res_2265_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___boxed(lean_object* v_00_u03b1_2266_, lean_object* v_bs_2267_, lean_object* v_k_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16(v_00_u03b1_2266_, v_bs_2267_, v_k_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec_ref(v_bs_2267_);
return v_res_2274_;
}
}
lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10(lean_object* v_00_u03b1_2275_, lean_object* v_bs_2276_, lean_object* v_k_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(v_bs_2276_, v_k_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
return v___x_2283_;
}
}
LEAN_EXPORT void l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_bs_2276_ = stack[1].m_obj;
lean_object* v_k_2277_ = stack[2].m_obj;
lean_object* v___y_2278_ = stack[3].m_obj;
lean_object* v___y_2279_ = stack[4].m_obj;
lean_object* v___y_2280_ = stack[5].m_obj;
lean_object* v___y_2281_ = stack[6].m_obj;
lean_object* v_res_2284_;
v_res_2284_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10(lean_box(0), v_bs_2276_, v_k_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
stack->m_obj
 = v_res_2284_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___boxed(lean_object* v_00_u03b1_2285_, lean_object* v_bs_2286_, lean_object* v_k_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10(v_00_u03b1_2285_, v_bs_2286_, v_k_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
return v_res_2293_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(lean_object* v_00_u03b1_2294_, lean_object* v_constName_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
return v___x_2301_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2295_ = stack[1].m_obj;
lean_object* v___y_2296_ = stack[2].m_obj;
lean_object* v___y_2297_ = stack[3].m_obj;
lean_object* v___y_2298_ = stack[4].m_obj;
lean_object* v___y_2299_ = stack[5].m_obj;
lean_object* v_res_2302_;
v_res_2302_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(lean_box(0), v_constName_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
stack->m_obj
 = v_res_2302_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2303_, lean_object* v_constName_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(v_00_u03b1_2303_, v_constName_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
return v_res_2310_;
}
}
lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(lean_object* v_00_u03b1_2311_, lean_object* v_msg_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
return v___x_2318_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2312_ = stack[1].m_obj;
lean_object* v___y_2313_ = stack[2].m_obj;
lean_object* v___y_2314_ = stack[3].m_obj;
lean_object* v___y_2315_ = stack[4].m_obj;
lean_object* v___y_2316_ = stack[5].m_obj;
lean_object* v_res_2319_;
v_res_2319_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(lean_box(0), v_msg_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
stack->m_obj
 = v_res_2319_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2320_, lean_object* v_msg_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(v_00_u03b1_2320_, v_msg_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
return v_res_2327_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7(lean_object* v_00_u03b1_2328_, lean_object* v_ref_2329_, lean_object* v_constName_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_2329_, v_constName_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
return v___x_2336_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2329_ = stack[1].m_obj;
lean_object* v_constName_2330_ = stack[2].m_obj;
lean_object* v___y_2331_ = stack[3].m_obj;
lean_object* v___y_2332_ = stack[4].m_obj;
lean_object* v___y_2333_ = stack[5].m_obj;
lean_object* v___y_2334_ = stack[6].m_obj;
lean_object* v_res_2337_;
v_res_2337_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7(lean_box(0), v_ref_2329_, v_constName_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
stack->m_obj
 = v_res_2337_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___boxed(lean_object* v_00_u03b1_2338_, lean_object* v_ref_2339_, lean_object* v_constName_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7(v_00_u03b1_2338_, v_ref_2339_, v_constName_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v_ref_2339_);
return v_res_2346_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18(lean_object* v_00_u03b1_2347_, lean_object* v_ref_2348_, lean_object* v_msg_2349_, lean_object* v_declHint_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v___x_2356_; 
v___x_2356_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg(v_ref_2348_, v_msg_2349_, v_declHint_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
return v___x_2356_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2348_ = stack[1].m_obj;
lean_object* v_msg_2349_ = stack[2].m_obj;
lean_object* v_declHint_2350_ = stack[3].m_obj;
lean_object* v___y_2351_ = stack[4].m_obj;
lean_object* v___y_2352_ = stack[5].m_obj;
lean_object* v___y_2353_ = stack[6].m_obj;
lean_object* v___y_2354_ = stack[7].m_obj;
lean_object* v_res_2357_;
v_res_2357_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18(lean_box(0), v_ref_2348_, v_msg_2349_, v_declHint_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
stack->m_obj
 = v_res_2357_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___boxed(lean_object* v_00_u03b1_2358_, lean_object* v_ref_2359_, lean_object* v_msg_2360_, lean_object* v_declHint_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18(v_00_u03b1_2358_, v_ref_2359_, v_msg_2360_, v_declHint_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v_ref_2359_);
return v_res_2367_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23(lean_object* v_msg_2368_, lean_object* v_declHint_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg(v_msg_2368_, v_declHint_2369_, v___y_2373_);
return v___x_2375_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2368_ = stack[0].m_obj;
lean_object* v_declHint_2369_ = stack[1].m_obj;
lean_object* v___y_2370_ = stack[2].m_obj;
lean_object* v___y_2371_ = stack[3].m_obj;
lean_object* v___y_2372_ = stack[4].m_obj;
lean_object* v___y_2373_ = stack[5].m_obj;
lean_object* v_res_2376_;
v_res_2376_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23(v_msg_2368_, v_declHint_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
stack->m_obj
 = v_res_2376_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___boxed(lean_object* v_msg_2377_, lean_object* v_declHint_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23(v_msg_2377_, v_declHint_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
return v_res_2384_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23(lean_object* v_00_u03b1_2385_, lean_object* v_ref_2386_, lean_object* v_msg_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg(v_ref_2386_, v_msg_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2393_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2386_ = stack[1].m_obj;
lean_object* v_msg_2387_ = stack[2].m_obj;
lean_object* v___y_2388_ = stack[3].m_obj;
lean_object* v___y_2389_ = stack[4].m_obj;
lean_object* v___y_2390_ = stack[5].m_obj;
lean_object* v___y_2391_ = stack[6].m_obj;
lean_object* v_res_2394_;
v_res_2394_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23(lean_box(0), v_ref_2386_, v_msg_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
stack->m_obj
 = v_res_2394_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___boxed(lean_object* v_00_u03b1_2395_, lean_object* v_ref_2396_, lean_object* v_msg_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23(v_00_u03b1_2395_, v_ref_2396_, v_msg_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v_ref_2396_);
return v_res_2403_;
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
