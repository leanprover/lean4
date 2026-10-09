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
v_isModule_683_ = lean_ctor_get_uint8(v___x_682_, sizeof(void*)*8 + 4);
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
v_isExporting_685_ = lean_ctor_get_uint8(v_env_681_, sizeof(void*)*13);
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
uint8_t v___x_20305__boxed_806_; uint8_t v___x_20306__boxed_807_; uint8_t v___x_20307__boxed_808_; lean_object* v_res_809_; 
v___x_20305__boxed_806_ = lean_unbox(v___x_796_);
v___x_20306__boxed_807_ = lean_unbox(v___x_797_);
v___x_20307__boxed_808_ = lean_unbox(v___x_798_);
v_res_809_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(v_cidx_795_, v___x_20305__boxed_806_, v___x_20306__boxed_807_, v___x_20307__boxed_808_, v_ys_799_, v_x_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
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
lean_object* v___x_816_; lean_object* v_env_817_; uint8_t v___x_818_; lean_object* v_env_819_; lean_object* v___x_820_; lean_object* v_toCold_821_; lean_object* v_mctx_822_; lean_object* v_lctx_823_; lean_object* v_options_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_816_ = lean_st_ref_get(v___y_814_);
v_env_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc_ref(v_env_817_);
lean_dec(v___x_816_);
v___x_818_ = 0;
v_env_819_ = l_Lean_Environment_setRecordingDeps(v_env_817_, v___x_818_);
v___x_820_ = lean_st_ref_get(v___y_812_);
v_toCold_821_ = lean_ctor_get(v___y_813_, 0);
v_mctx_822_ = lean_ctor_get(v___x_820_, 0);
lean_inc_ref(v_mctx_822_);
lean_dec(v___x_820_);
v_lctx_823_ = lean_ctor_get(v___y_811_, 2);
v_options_824_ = lean_ctor_get(v_toCold_821_, 2);
lean_inc_ref(v_options_824_);
lean_inc_ref(v_lctx_823_);
v___x_825_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_825_, 0, v_env_819_);
lean_ctor_set(v___x_825_, 1, v_mctx_822_);
lean_ctor_set(v___x_825_, 2, v_lctx_823_);
lean_ctor_set(v___x_825_, 3, v_options_824_);
v___x_826_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
lean_ctor_set(v___x_826_, 1, v_msgData_810_);
v___x_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11___boxed(lean_object* v_msgData_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(v_msgData_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(lean_object* v_msg_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_ref_841_; lean_object* v___x_842_; lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_851_; 
v_ref_841_ = lean_ctor_get(v___y_838_, 2);
v___x_842_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(v_msg_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_851_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_851_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_851_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_849_; 
lean_inc(v_ref_841_);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v_ref_841_);
lean_ctor_set(v___x_847_, 1, v_a_843_);
if (v_isShared_846_ == 0)
{
lean_ctor_set_tag(v___x_845_, 1);
lean_ctor_set(v___x_845_, 0, v___x_847_);
v___x_849_ = v___x_845_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg___boxed(lean_object* v_msg_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
return v_res_858_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0(void){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_instMonadEIO___redArg();
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(lean_object* v_msg_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v_toApplicative_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_933_; 
v___x_870_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0);
v___x_871_ = l_StateRefT_x27_instMonad___redArg(v___x_870_);
v_toApplicative_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_933_ == 0)
{
lean_object* v_unused_934_; 
v_unused_934_ = lean_ctor_get(v___x_871_, 1);
lean_dec(v_unused_934_);
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_933_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_toApplicative_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_933_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v_toFunctor_876_; lean_object* v_toSeq_877_; lean_object* v_toSeqLeft_878_; lean_object* v_toSeqRight_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_931_; 
v_toFunctor_876_ = lean_ctor_get(v_toApplicative_872_, 0);
v_toSeq_877_ = lean_ctor_get(v_toApplicative_872_, 2);
v_toSeqLeft_878_ = lean_ctor_get(v_toApplicative_872_, 3);
v_toSeqRight_879_ = lean_ctor_get(v_toApplicative_872_, 4);
v_isSharedCheck_931_ = !lean_is_exclusive(v_toApplicative_872_);
if (v_isSharedCheck_931_ == 0)
{
lean_object* v_unused_932_; 
v_unused_932_ = lean_ctor_get(v_toApplicative_872_, 1);
lean_dec(v_unused_932_);
v___x_881_ = v_toApplicative_872_;
v_isShared_882_ = v_isSharedCheck_931_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_toSeqRight_879_);
lean_inc(v_toSeqLeft_878_);
lean_inc(v_toSeq_877_);
lean_inc(v_toFunctor_876_);
lean_dec(v_toApplicative_872_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_931_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___f_883_; lean_object* v___f_884_; lean_object* v___f_885_; lean_object* v___f_886_; lean_object* v___x_887_; lean_object* v___f_888_; lean_object* v___f_889_; lean_object* v___f_890_; lean_object* v___x_892_; 
v___f_883_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__1));
v___f_884_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__2));
lean_inc_ref(v_toFunctor_876_);
v___f_885_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_885_, 0, v_toFunctor_876_);
v___f_886_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_886_, 0, v_toFunctor_876_);
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v___f_885_);
lean_ctor_set(v___x_887_, 1, v___f_886_);
v___f_888_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_888_, 0, v_toSeqRight_879_);
v___f_889_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_889_, 0, v_toSeqLeft_878_);
v___f_890_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_890_, 0, v_toSeq_877_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 4, v___f_888_);
lean_ctor_set(v___x_881_, 3, v___f_889_);
lean_ctor_set(v___x_881_, 2, v___f_890_);
lean_ctor_set(v___x_881_, 1, v___f_883_);
lean_ctor_set(v___x_881_, 0, v___x_887_);
v___x_892_ = v___x_881_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v___f_883_);
lean_ctor_set(v_reuseFailAlloc_930_, 2, v___f_890_);
lean_ctor_set(v_reuseFailAlloc_930_, 3, v___f_889_);
lean_ctor_set(v_reuseFailAlloc_930_, 4, v___f_888_);
v___x_892_ = v_reuseFailAlloc_930_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_894_; 
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 1, v___f_884_);
lean_ctor_set(v___x_874_, 0, v___x_892_);
v___x_894_ = v___x_874_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v___f_884_);
v___x_894_ = v_reuseFailAlloc_929_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; lean_object* v_toApplicative_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_927_; 
v___x_895_ = l_StateRefT_x27_instMonad___redArg(v___x_894_);
v_toApplicative_896_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_927_ == 0)
{
lean_object* v_unused_928_; 
v_unused_928_ = lean_ctor_get(v___x_895_, 1);
lean_dec(v_unused_928_);
v___x_898_ = v___x_895_;
v_isShared_899_ = v_isSharedCheck_927_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_toApplicative_896_);
lean_dec(v___x_895_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_927_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_toFunctor_900_; lean_object* v_toSeq_901_; lean_object* v_toSeqLeft_902_; lean_object* v_toSeqRight_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_925_; 
v_toFunctor_900_ = lean_ctor_get(v_toApplicative_896_, 0);
v_toSeq_901_ = lean_ctor_get(v_toApplicative_896_, 2);
v_toSeqLeft_902_ = lean_ctor_get(v_toApplicative_896_, 3);
v_toSeqRight_903_ = lean_ctor_get(v_toApplicative_896_, 4);
v_isSharedCheck_925_ = !lean_is_exclusive(v_toApplicative_896_);
if (v_isSharedCheck_925_ == 0)
{
lean_object* v_unused_926_; 
v_unused_926_ = lean_ctor_get(v_toApplicative_896_, 1);
lean_dec(v_unused_926_);
v___x_905_ = v_toApplicative_896_;
v_isShared_906_ = v_isSharedCheck_925_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_toSeqRight_903_);
lean_inc(v_toSeqLeft_902_);
lean_inc(v_toSeq_901_);
lean_inc(v_toFunctor_900_);
lean_dec(v_toApplicative_896_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_925_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___f_907_; lean_object* v___f_908_; lean_object* v___f_909_; lean_object* v___f_910_; lean_object* v___x_911_; lean_object* v___f_912_; lean_object* v___f_913_; lean_object* v___f_914_; lean_object* v___x_916_; 
v___f_907_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__3));
v___f_908_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__4));
lean_inc_ref(v_toFunctor_900_);
v___f_909_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_909_, 0, v_toFunctor_900_);
v___f_910_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_910_, 0, v_toFunctor_900_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v___f_909_);
lean_ctor_set(v___x_911_, 1, v___f_910_);
v___f_912_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_912_, 0, v_toSeqRight_903_);
v___f_913_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_913_, 0, v_toSeqLeft_902_);
v___f_914_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_914_, 0, v_toSeq_901_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 4, v___f_912_);
lean_ctor_set(v___x_905_, 3, v___f_913_);
lean_ctor_set(v___x_905_, 2, v___f_914_);
lean_ctor_set(v___x_905_, 1, v___f_907_);
lean_ctor_set(v___x_905_, 0, v___x_911_);
v___x_916_ = v___x_905_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_911_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v___f_907_);
lean_ctor_set(v_reuseFailAlloc_924_, 2, v___f_914_);
lean_ctor_set(v_reuseFailAlloc_924_, 3, v___f_913_);
lean_ctor_set(v_reuseFailAlloc_924_, 4, v___f_912_);
v___x_916_ = v_reuseFailAlloc_924_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_918_; 
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v___f_908_);
lean_ctor_set(v___x_898_, 0, v___x_916_);
v___x_918_ = v___x_898_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v___f_908_);
v___x_918_ = v_reuseFailAlloc_923_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_16397__overap_921_; lean_object* v___x_922_; 
v___x_919_ = lean_box(0);
v___x_920_ = l_instInhabitedOfMonad___redArg(v___x_918_, v___x_919_);
v___x_16397__overap_921_ = lean_panic_fn_borrowed(v___x_920_, v_msg_864_);
lean_dec(v___x_920_);
lean_inc(v___y_868_);
lean_inc_ref(v___y_867_);
lean_inc(v___y_866_);
lean_inc_ref(v___y_865_);
v___x_922_ = lean_apply_5(v___x_16397__overap_921_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, lean_box(0));
return v___x_922_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___boxed(lean_object* v_msg_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(v_msg_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
return v_res_941_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__0));
v___x_944_ = l_Lean_stringToMessageData(v___x_943_);
return v___x_944_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__2));
v___x_947_ = l_Lean_stringToMessageData(v___x_946_);
return v___x_947_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_951_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6));
v___x_952_ = lean_unsigned_to_nat(11u);
v___x_953_ = lean_unsigned_to_nat(122u);
v___x_954_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__5));
v___x_955_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__4));
v___x_956_ = l_mkPanicMessageWithDecl(v___x_955_, v___x_954_, v___x_953_, v___x_952_, v___x_951_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(lean_object* v_constName_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v___x_971_; lean_object* v_env_972_; uint8_t v___x_973_; lean_object* v___x_974_; 
v___x_971_ = lean_st_ref_get(v___y_961_);
v_env_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc_ref(v_env_972_);
lean_dec(v___x_971_);
v___x_973_ = 0;
lean_inc(v_constName_957_);
v___x_974_ = l_Lean_Environment_findAsync_x3f(v_env_972_, v_constName_957_, v___x_973_);
if (lean_obj_tag(v___x_974_) == 1)
{
lean_object* v_val_975_; uint8_t v_kind_976_; 
v_val_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_val_975_);
lean_dec_ref_known(v___x_974_, 1);
v_kind_976_ = lean_ctor_get_uint8(v_val_975_, sizeof(void*)*3);
if (v_kind_976_ == 6)
{
lean_object* v___x_977_; 
v___x_977_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_975_);
if (lean_obj_tag(v___x_977_) == 6)
{
lean_object* v_val_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec(v_constName_957_);
v_val_978_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_977_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_val_978_);
lean_dec(v___x_977_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
lean_ctor_set_tag(v___x_980_, 0);
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_val_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; 
lean_dec_ref(v___x_977_);
v___x_986_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7);
v___x_987_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(v___x_986_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_996_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_996_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_996_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_996_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
if (lean_obj_tag(v_a_988_) == 0)
{
lean_del_object(v___x_990_);
goto v___jp_963_;
}
else
{
lean_object* v_val_992_; lean_object* v___x_994_; 
lean_dec(v_constName_957_);
v_val_992_ = lean_ctor_get(v_a_988_, 0);
lean_inc(v_val_992_);
lean_dec_ref_known(v_a_988_, 1);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v_val_992_);
v___x_994_ = v___x_990_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_val_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec(v_constName_957_);
v_a_997_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_987_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_987_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
}
else
{
lean_dec(v_val_975_);
goto v___jp_963_;
}
}
else
{
lean_dec(v___x_974_);
goto v___jp_963_;
}
v___jp_963_:
{
lean_object* v___x_964_; uint8_t v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_964_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1);
v___x_965_ = 0;
v___x_966_ = l_Lean_MessageData_ofConstName(v_constName_957_, v___x_965_);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_964_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v___x_969_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
return v___x_970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___boxed(lean_object* v_constName_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(v_constName_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(uint8_t v___x_1012_, lean_object* v___x_1013_, lean_object* v_as_x27_1014_, lean_object* v_b_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
if (lean_obj_tag(v_as_x27_1014_) == 0)
{
lean_object* v___x_1021_; 
v___x_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1021_, 0, v_b_1015_);
return v___x_1021_;
}
else
{
lean_object* v_head_1022_; lean_object* v_tail_1023_; uint8_t v___x_1024_; uint8_t v___x_1025_; lean_object* v___x_1026_; 
v_head_1022_ = lean_ctor_get(v_as_x27_1014_, 0);
v_tail_1023_ = lean_ctor_get(v_as_x27_1014_, 1);
v___x_1024_ = 0;
v___x_1025_ = 1;
lean_inc(v_head_1022_);
v___x_1026_ = l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(v_head_1022_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v_toConstantVal_1028_; lean_object* v_cidx_1029_; lean_object* v_numFields_1030_; lean_object* v_type_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___f_1035_; lean_object* v___x_1036_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec_ref_known(v___x_1026_, 1);
v_toConstantVal_1028_ = lean_ctor_get(v_a_1027_, 0);
lean_inc_ref(v_toConstantVal_1028_);
v_cidx_1029_ = lean_ctor_get(v_a_1027_, 2);
lean_inc(v_cidx_1029_);
v_numFields_1030_ = lean_ctor_get(v_a_1027_, 4);
lean_inc(v_numFields_1030_);
lean_dec(v_a_1027_);
v_type_1031_ = lean_ctor_get(v_toConstantVal_1028_, 2);
lean_inc_ref(v_type_1031_);
lean_dec_ref(v_toConstantVal_1028_);
v___x_1032_ = lean_box(v___x_1024_);
v___x_1033_ = lean_box(v___x_1012_);
v___x_1034_ = lean_box(v___x_1025_);
v___f_1035_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1035_, 0, v_cidx_1029_);
lean_closure_set(v___f_1035_, 1, v___x_1032_);
lean_closure_set(v___f_1035_, 2, v___x_1033_);
lean_closure_set(v___f_1035_, 3, v___x_1034_);
v___x_1036_ = l_Lean_Meta_instantiateForall(v_type_1031_, v___x_1013_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1048_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1039_ = v___x_1036_;
v_isShared_1040_ = v_isSharedCheck_1048_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1036_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1048_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set_tag(v___x_1039_, 1);
lean_ctor_set(v___x_1039_, 0, v_numFields_1030_);
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_numFields_1030_);
v___x_1042_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_a_1037_, v___x_1042_, v___f_1035_, v___x_1024_, v___x_1024_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_a_1044_; lean_object* v___x_1045_; 
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_a_1044_);
lean_dec_ref_known(v___x_1043_, 1);
v___x_1045_ = l_Lean_Expr_app___override(v_b_1015_, v_a_1044_);
v_as_x27_1014_ = v_tail_1023_;
v_b_1015_ = v___x_1045_;
goto _start;
}
else
{
lean_dec_ref(v_b_1015_);
return v___x_1043_;
}
}
}
}
else
{
lean_dec_ref(v___f_1035_);
lean_dec(v_numFields_1030_);
lean_dec_ref(v_b_1015_);
return v___x_1036_;
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec_ref(v_b_1015_);
v_a_1049_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1026_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1026_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___boxed(lean_object* v___x_1057_, lean_object* v___x_1058_, lean_object* v_as_x27_1059_, lean_object* v_b_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
uint8_t v___x_20679__boxed_1066_; lean_object* v_res_1067_; 
v___x_20679__boxed_1066_ = lean_unbox(v___x_1057_);
v_res_1067_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_20679__boxed_1066_, v___x_1058_, v_as_x27_1059_, v_b_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v_as_x27_1059_);
lean_dec_ref(v___x_1058_);
return v_res_1067_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_box(0);
v___x_1069_ = l_Lean_Level_succ___override(v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0(lean_object* v_xs_1070_, uint8_t v___x_1071_, uint8_t v___x_1072_, uint8_t v___x_1073_, lean_object* v_val_1074_, lean_object* v___x_1075_, lean_object* v___x_1076_, lean_object* v___x_1077_, lean_object* v___x_1078_, lean_object* v___x_1079_, lean_object* v_ctors_1080_, lean_object* v___x_1081_, lean_object* v_x_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v_value_1089_; lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; 
v___x_1092_ = l_Lean_InductiveVal_numCtors(v_val_1074_);
v___x_1093_ = lean_unsigned_to_nat(1u);
v___x_1094_ = lean_nat_dec_eq(v___x_1092_, v___x_1093_);
lean_dec(v___x_1092_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec(v___x_1081_);
lean_inc_ref(v_x_1082_);
lean_inc_ref(v___x_1075_);
v___x_1095_ = lean_array_push(v___x_1075_, v_x_1082_);
v___x_1096_ = l_Lean_Meta_mkLambdaFVars(v___x_1095_, v___x_1076_, v___x_1071_, v___x_1072_, v___x_1071_, v___x_1072_, v___x_1073_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec_ref(v___x_1095_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v___x_1096_, 1);
v___x_1098_ = lean_obj_once(&l_Lean_mkCtorIdx___lam__0___closed__0, &l_Lean_mkCtorIdx___lam__0___closed__0_once, _init_l_Lean_mkCtorIdx___lam__0___closed__0);
v___x_1099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v___x_1077_);
v___x_1100_ = l_Lean_mkConst(v___x_1078_, v___x_1099_);
v___x_1101_ = l_Lean_mkAppN(v___x_1100_, v___x_1079_);
v___x_1102_ = l_Lean_Expr_app___override(v___x_1101_, v_a_1097_);
v___x_1103_ = l_Lean_mkAppN(v___x_1102_, v___x_1075_);
lean_dec_ref(v___x_1075_);
lean_inc_ref(v_x_1082_);
v___x_1104_ = l_Lean_Expr_app___override(v___x_1103_, v_x_1082_);
v___x_1105_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_1072_, v___x_1079_, v_ctors_1080_, v___x_1104_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v_value_1089_ = v_a_1106_;
goto v___jp_1088_;
}
else
{
lean_dec_ref(v_x_1082_);
lean_dec_ref(v_xs_1070_);
return v___x_1105_;
}
}
else
{
lean_dec_ref(v_x_1082_);
lean_dec(v___x_1078_);
lean_dec(v___x_1077_);
lean_dec_ref(v___x_1075_);
lean_dec_ref(v_xs_1070_);
return v___x_1096_;
}
}
else
{
lean_object* v___x_1107_; 
lean_dec(v___x_1078_);
lean_dec(v___x_1077_);
lean_dec_ref(v___x_1076_);
lean_dec_ref(v___x_1075_);
v___x_1107_ = l_Lean_mkRawNatLit(v___x_1081_);
v_value_1089_ = v___x_1107_;
goto v___jp_1088_;
}
v___jp_1088_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_array_push(v_xs_1070_, v_x_1082_);
v___x_1091_ = l_Lean_Meta_mkLambdaFVars(v___x_1090_, v_value_1089_, v___x_1071_, v___x_1072_, v___x_1071_, v___x_1072_, v___x_1073_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec_ref(v___x_1090_);
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0___boxed(lean_object** _args){
lean_object* v_xs_1108_ = _args[0];
lean_object* v___x_1109_ = _args[1];
lean_object* v___x_1110_ = _args[2];
lean_object* v___x_1111_ = _args[3];
lean_object* v_val_1112_ = _args[4];
lean_object* v___x_1113_ = _args[5];
lean_object* v___x_1114_ = _args[6];
lean_object* v___x_1115_ = _args[7];
lean_object* v___x_1116_ = _args[8];
lean_object* v___x_1117_ = _args[9];
lean_object* v_ctors_1118_ = _args[10];
lean_object* v___x_1119_ = _args[11];
lean_object* v_x_1120_ = _args[12];
lean_object* v___y_1121_ = _args[13];
lean_object* v___y_1122_ = _args[14];
lean_object* v___y_1123_ = _args[15];
lean_object* v___y_1124_ = _args[16];
lean_object* v___y_1125_ = _args[17];
_start:
{
uint8_t v___x_20770__boxed_1126_; uint8_t v___x_20771__boxed_1127_; uint8_t v___x_20772__boxed_1128_; lean_object* v_res_1129_; 
v___x_20770__boxed_1126_ = lean_unbox(v___x_1109_);
v___x_20771__boxed_1127_ = lean_unbox(v___x_1110_);
v___x_20772__boxed_1128_ = lean_unbox(v___x_1111_);
v_res_1129_ = l_Lean_mkCtorIdx___lam__0(v_xs_1108_, v___x_20770__boxed_1126_, v___x_20771__boxed_1127_, v___x_20772__boxed_1128_, v_val_1112_, v___x_1113_, v___x_1114_, v___x_1115_, v___x_1116_, v___x_1117_, v_ctors_1118_, v___x_1119_, v_x_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v_ctors_1118_);
lean_dec_ref(v___x_1117_);
lean_dec_ref(v_val_1112_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(lean_object* v_k_1130_, lean_object* v_b_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___x_1137_; 
lean_inc(v___y_1135_);
lean_inc_ref(v___y_1134_);
lean_inc(v___y_1133_);
lean_inc_ref(v___y_1132_);
v___x_1137_ = lean_apply_6(v_k_1130_, v_b_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, lean_box(0));
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(lean_object* v_k_1138_, lean_object* v_b_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(v_k_1138_, v_b_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(lean_object* v_name_1146_, uint8_t v_bi_1147_, lean_object* v_type_1148_, lean_object* v_k_1149_, uint8_t v_kind_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___f_1156_; lean_object* v___x_1157_; 
v___f_1156_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1156_, 0, v_k_1149_);
v___x_1157_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1146_, v_bi_1147_, v_type_1148_, v___f_1156_, v_kind_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
v_a_1166_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1157_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1157_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___boxed(lean_object* v_name_1174_, lean_object* v_bi_1175_, lean_object* v_type_1176_, lean_object* v_k_1177_, lean_object* v_kind_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
uint8_t v_bi_boxed_1184_; uint8_t v_kind_boxed_1185_; lean_object* v_res_1186_; 
v_bi_boxed_1184_ = lean_unbox(v_bi_1175_);
v_kind_boxed_1185_ = lean_unbox(v_kind_1178_);
v_res_1186_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_1174_, v_bi_boxed_1184_, v_type_1176_, v_k_1177_, v_kind_boxed_1185_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(lean_object* v_name_1187_, lean_object* v_type_1188_, lean_object* v_k_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
uint8_t v___x_1195_; uint8_t v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = 0;
v___x_1196_ = 0;
v___x_1197_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_1187_, v___x_1195_, v_type_1188_, v_k_1189_, v___x_1196_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg___boxed(lean_object* v_name_1198_, lean_object* v_type_1199_, lean_object* v_k_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v_name_1198_, v_type_1199_, v_k_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(lean_object* v_env_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v___x_1211_; lean_object* v_nextMacroScope_1212_; lean_object* v_ngen_1213_; lean_object* v_auxDeclNGen_1214_; lean_object* v_traceState_1215_; lean_object* v_recordedDeps_1216_; lean_object* v_messages_1217_; lean_object* v_infoState_1218_; lean_object* v_snapshotTasks_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1245_; 
v___x_1211_ = lean_st_ref_take(v___y_1209_);
v_nextMacroScope_1212_ = lean_ctor_get(v___x_1211_, 1);
v_ngen_1213_ = lean_ctor_get(v___x_1211_, 2);
v_auxDeclNGen_1214_ = lean_ctor_get(v___x_1211_, 3);
v_traceState_1215_ = lean_ctor_get(v___x_1211_, 4);
v_recordedDeps_1216_ = lean_ctor_get(v___x_1211_, 6);
v_messages_1217_ = lean_ctor_get(v___x_1211_, 7);
v_infoState_1218_ = lean_ctor_get(v___x_1211_, 8);
v_snapshotTasks_1219_ = lean_ctor_get(v___x_1211_, 9);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; lean_object* v_unused_1247_; 
v_unused_1246_ = lean_ctor_get(v___x_1211_, 5);
lean_dec(v_unused_1246_);
v_unused_1247_ = lean_ctor_get(v___x_1211_, 0);
lean_dec(v_unused_1247_);
v___x_1221_ = v___x_1211_;
v_isShared_1222_ = v_isSharedCheck_1245_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_snapshotTasks_1219_);
lean_inc(v_infoState_1218_);
lean_inc(v_messages_1217_);
lean_inc(v_recordedDeps_1216_);
lean_inc(v_traceState_1215_);
lean_inc(v_auxDeclNGen_1214_);
lean_inc(v_ngen_1213_);
lean_inc(v_nextMacroScope_1212_);
lean_dec(v___x_1211_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1245_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1223_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 5, v___x_1223_);
lean_ctor_set(v___x_1221_, 0, v_env_1207_);
v___x_1225_ = v___x_1221_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_env_1207_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_nextMacroScope_1212_);
lean_ctor_set(v_reuseFailAlloc_1244_, 2, v_ngen_1213_);
lean_ctor_set(v_reuseFailAlloc_1244_, 3, v_auxDeclNGen_1214_);
lean_ctor_set(v_reuseFailAlloc_1244_, 4, v_traceState_1215_);
lean_ctor_set(v_reuseFailAlloc_1244_, 5, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1244_, 6, v_recordedDeps_1216_);
lean_ctor_set(v_reuseFailAlloc_1244_, 7, v_messages_1217_);
lean_ctor_set(v_reuseFailAlloc_1244_, 8, v_infoState_1218_);
lean_ctor_set(v_reuseFailAlloc_1244_, 9, v_snapshotTasks_1219_);
v___x_1225_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v_mctx_1228_; lean_object* v_zetaDeltaFVarIds_1229_; lean_object* v_postponed_1230_; lean_object* v_diag_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1242_; 
v___x_1226_ = lean_st_ref_put(v___y_1209_, v___x_1225_);
v___x_1227_ = lean_st_ref_take(v___y_1208_);
v_mctx_1228_ = lean_ctor_get(v___x_1227_, 0);
v_zetaDeltaFVarIds_1229_ = lean_ctor_get(v___x_1227_, 2);
v_postponed_1230_ = lean_ctor_get(v___x_1227_, 3);
v_diag_1231_ = lean_ctor_get(v___x_1227_, 4);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v___x_1227_, 1);
lean_dec(v_unused_1243_);
v___x_1233_ = v___x_1227_;
v_isShared_1234_ = v_isSharedCheck_1242_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_diag_1231_);
lean_inc(v_postponed_1230_);
lean_inc(v_zetaDeltaFVarIds_1229_);
lean_inc(v_mctx_1228_);
lean_dec(v___x_1227_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1242_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1238_; 
v___x_1235_ = lean_box(0);
v___x_1236_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 1, v___x_1236_);
v___x_1238_ = v___x_1233_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_mctx_1228_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1241_, 2, v_zetaDeltaFVarIds_1229_);
lean_ctor_set(v_reuseFailAlloc_1241_, 3, v_postponed_1230_);
lean_ctor_set(v_reuseFailAlloc_1241_, 4, v_diag_1231_);
v___x_1238_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = lean_st_ref_put(v___y_1208_, v___x_1238_);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1235_);
return v___x_1240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg___boxed(lean_object* v_env_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(v_env_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec(v___y_1249_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9(lean_object* v_declName_1253_, lean_object* v_impName_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; lean_object* v_env_1261_; lean_object* v___x_1262_; 
v___x_1260_ = lean_st_ref_get(v___y_1258_);
v_env_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc_ref(v_env_1261_);
lean_dec(v___x_1260_);
v___x_1262_ = l_Lean_Compiler_setImplementedBy(v_env_1261_, v_declName_1253_, v_impName_1254_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1272_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1265_ = v___x_1262_;
v_isShared_1266_ = v_isSharedCheck_1272_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1272_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
lean_ctor_set_tag(v___x_1265_, 3);
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = l_Lean_MessageData_ofFormat(v___x_1268_);
v___x_1270_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v___x_1269_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
return v___x_1270_;
}
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1274_; 
v_a_1273_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1262_, 1);
v___x_1274_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(v_a_1273_, v___y_1256_, v___y_1258_);
return v___x_1274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9___boxed(lean_object* v_declName_1275_, lean_object* v_impName_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9(v_declName_1275_, v_impName_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1(lean_object* v___x_1286_, lean_object* v___x_1287_, lean_object* v_xs_1288_, uint8_t v___x_1289_, uint8_t v___x_1290_, lean_object* v_val_1291_, lean_object* v___x_1292_, lean_object* v___x_1293_, lean_object* v___x_1294_, lean_object* v___x_1295_, lean_object* v_ctors_1296_, lean_object* v___x_1297_, lean_object* v___x_1298_, lean_object* v_levelParams_1299_, lean_object* v_indName_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___x_1306_; 
lean_inc_ref(v___x_1287_);
lean_inc_ref(v___x_1286_);
v___x_1306_ = l_Lean_mkArrow(v___x_1286_, v___x_1287_, v___y_1303_, v___y_1304_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; uint8_t v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___f_1312_; lean_object* v___x_1313_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
lean_dec_ref_known(v___x_1306_, 1);
v___x_1308_ = 1;
v___x_1309_ = lean_box(v___x_1289_);
v___x_1310_ = lean_box(v___x_1290_);
v___x_1311_ = lean_box(v___x_1308_);
lean_inc_ref(v_val_1291_);
lean_inc_ref(v_xs_1288_);
v___f_1312_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1312_, 0, v_xs_1288_);
lean_closure_set(v___f_1312_, 1, v___x_1309_);
lean_closure_set(v___f_1312_, 2, v___x_1310_);
lean_closure_set(v___f_1312_, 3, v___x_1311_);
lean_closure_set(v___f_1312_, 4, v_val_1291_);
lean_closure_set(v___f_1312_, 5, v___x_1292_);
lean_closure_set(v___f_1312_, 6, v___x_1287_);
lean_closure_set(v___f_1312_, 7, v___x_1293_);
lean_closure_set(v___f_1312_, 8, v___x_1294_);
lean_closure_set(v___f_1312_, 9, v___x_1295_);
lean_closure_set(v___f_1312_, 10, v_ctors_1296_);
lean_closure_set(v___f_1312_, 11, v___x_1297_);
v___x_1313_ = l_Lean_Meta_mkForallFVars(v_xs_1288_, v_a_1307_, v___x_1289_, v___x_1290_, v___x_1290_, v___x_1308_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec_ref(v_xs_1288_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
lean_dec_ref_known(v___x_1313_, 1);
v___x_1315_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__1___closed__1));
v___x_1316_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v___x_1315_, v___x_1286_, v___f_1312_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1318_; lean_object* v_env_1319_; uint32_t v___x_1320_; lean_object* v___x_1321_; uint32_t v___x_1322_; uint32_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1467_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc_n(v_a_1317_, 2);
lean_dec_ref_known(v___x_1316_, 1);
v___x_1318_ = lean_st_ref_get(v___y_1304_);
v_env_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc_ref(v_env_1319_);
lean_dec(v___x_1318_);
v___x_1320_ = l_Lean_getMaxHeight(v_env_1319_, v_a_1317_);
v___x_1321_ = lean_unsigned_to_nat(1u);
v___x_1322_ = 1;
v___x_1323_ = lean_uint32_add(v___x_1320_, v___x_1322_);
v___x_1324_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_1324_, 0, v___x_1323_);
lean_inc(v_a_1314_);
lean_inc(v_levelParams_1299_);
lean_inc(v___x_1298_);
v___x_1325_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v___x_1298_, v_levelParams_1299_, v_a_1314_, v_a_1317_, v___x_1324_, v___y_1304_);
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1328_ = v___x_1325_;
v_isShared_1329_ = v_isSharedCheck_1467_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1325_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1467_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
lean_ctor_set_tag(v___x_1328_, 1);
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___x_1358_; 
lean_inc_ref(v___x_1331_);
v___x_1358_ = l_Lean_addDecl(v___x_1331_, v___x_1289_, v___y_1303_, v___y_1304_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v___x_1359_; lean_object* v_env_1360_; lean_object* v_nextMacroScope_1361_; lean_object* v_ngen_1362_; lean_object* v_auxDeclNGen_1363_; lean_object* v_traceState_1364_; lean_object* v_recordedDeps_1365_; lean_object* v_messages_1366_; lean_object* v_infoState_1367_; lean_object* v_snapshotTasks_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1464_; 
lean_dec_ref_known(v___x_1358_, 1);
v___x_1359_ = lean_st_ref_take(v___y_1304_);
v_env_1360_ = lean_ctor_get(v___x_1359_, 0);
v_nextMacroScope_1361_ = lean_ctor_get(v___x_1359_, 1);
v_ngen_1362_ = lean_ctor_get(v___x_1359_, 2);
v_auxDeclNGen_1363_ = lean_ctor_get(v___x_1359_, 3);
v_traceState_1364_ = lean_ctor_get(v___x_1359_, 4);
v_recordedDeps_1365_ = lean_ctor_get(v___x_1359_, 6);
v_messages_1366_ = lean_ctor_get(v___x_1359_, 7);
v_infoState_1367_ = lean_ctor_get(v___x_1359_, 8);
v_snapshotTasks_1368_ = lean_ctor_get(v___x_1359_, 9);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1464_ == 0)
{
lean_object* v_unused_1465_; 
v_unused_1465_ = lean_ctor_get(v___x_1359_, 5);
lean_dec(v_unused_1465_);
v___x_1370_ = v___x_1359_;
v_isShared_1371_ = v_isSharedCheck_1464_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_snapshotTasks_1368_);
lean_inc(v_infoState_1367_);
lean_inc(v_messages_1366_);
lean_inc(v_recordedDeps_1365_);
lean_inc(v_traceState_1364_);
lean_inc(v_auxDeclNGen_1363_);
lean_inc(v_ngen_1362_);
lean_inc(v_nextMacroScope_1361_);
lean_inc(v_env_1360_);
lean_dec(v___x_1359_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1464_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
lean_inc(v___x_1298_);
v___x_1372_ = l_Lean_Meta_addToCompletionBlackList(v_env_1360_, v___x_1298_);
v___x_1373_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__3);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 5, v___x_1373_);
lean_ctor_set(v___x_1370_, 0, v___x_1372_);
v___x_1375_ = v___x_1370_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_nextMacroScope_1361_);
lean_ctor_set(v_reuseFailAlloc_1463_, 2, v_ngen_1362_);
lean_ctor_set(v_reuseFailAlloc_1463_, 3, v_auxDeclNGen_1363_);
lean_ctor_set(v_reuseFailAlloc_1463_, 4, v_traceState_1364_);
lean_ctor_set(v_reuseFailAlloc_1463_, 5, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1463_, 6, v_recordedDeps_1365_);
lean_ctor_set(v_reuseFailAlloc_1463_, 7, v_messages_1366_);
lean_ctor_set(v_reuseFailAlloc_1463_, 8, v_infoState_1367_);
lean_ctor_set(v_reuseFailAlloc_1463_, 9, v_snapshotTasks_1368_);
v___x_1375_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v_mctx_1378_; lean_object* v_zetaDeltaFVarIds_1379_; lean_object* v_postponed_1380_; lean_object* v_diag_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1461_; 
v___x_1376_ = lean_st_ref_put(v___y_1304_, v___x_1375_);
v___x_1377_ = lean_st_ref_take(v___y_1302_);
v_mctx_1378_ = lean_ctor_get(v___x_1377_, 0);
v_zetaDeltaFVarIds_1379_ = lean_ctor_get(v___x_1377_, 2);
v_postponed_1380_ = lean_ctor_get(v___x_1377_, 3);
v_diag_1381_ = lean_ctor_get(v___x_1377_, 4);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v___x_1377_, 1);
lean_dec(v_unused_1462_);
v___x_1383_ = v___x_1377_;
v_isShared_1384_ = v_isSharedCheck_1461_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_diag_1381_);
lean_inc(v_postponed_1380_);
lean_inc(v_zetaDeltaFVarIds_1379_);
lean_inc(v_mctx_1378_);
lean_dec(v___x_1377_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1461_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1385_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__4);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 1, v___x_1385_);
v___x_1387_ = v___x_1383_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_mctx_1378_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v_zetaDeltaFVarIds_1379_);
lean_ctor_set(v_reuseFailAlloc_1460_, 3, v_postponed_1380_);
lean_ctor_set(v_reuseFailAlloc_1460_, 4, v_diag_1381_);
v___x_1387_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v_env_1390_; lean_object* v_nextMacroScope_1391_; lean_object* v_ngen_1392_; lean_object* v_auxDeclNGen_1393_; lean_object* v_traceState_1394_; lean_object* v_recordedDeps_1395_; lean_object* v_messages_1396_; lean_object* v_infoState_1397_; lean_object* v_snapshotTasks_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1458_; 
v___x_1388_ = lean_st_ref_put(v___y_1302_, v___x_1387_);
v___x_1389_ = lean_st_ref_take(v___y_1304_);
v_env_1390_ = lean_ctor_get(v___x_1389_, 0);
v_nextMacroScope_1391_ = lean_ctor_get(v___x_1389_, 1);
v_ngen_1392_ = lean_ctor_get(v___x_1389_, 2);
v_auxDeclNGen_1393_ = lean_ctor_get(v___x_1389_, 3);
v_traceState_1394_ = lean_ctor_get(v___x_1389_, 4);
v_recordedDeps_1395_ = lean_ctor_get(v___x_1389_, 6);
v_messages_1396_ = lean_ctor_get(v___x_1389_, 7);
v_infoState_1397_ = lean_ctor_get(v___x_1389_, 8);
v_snapshotTasks_1398_ = lean_ctor_get(v___x_1389_, 9);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; 
v_unused_1459_ = lean_ctor_get(v___x_1389_, 5);
lean_dec(v_unused_1459_);
v___x_1400_ = v___x_1389_;
v_isShared_1401_ = v_isSharedCheck_1458_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_snapshotTasks_1398_);
lean_inc(v_infoState_1397_);
lean_inc(v_messages_1396_);
lean_inc(v_recordedDeps_1395_);
lean_inc(v_traceState_1394_);
lean_inc(v_auxDeclNGen_1393_);
lean_inc(v_ngen_1392_);
lean_inc(v_nextMacroScope_1391_);
lean_inc(v_env_1390_);
lean_dec(v___x_1389_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1458_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
lean_inc(v___x_1298_);
v___x_1402_ = l_Lean_addProtected(v_env_1390_, v___x_1298_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 5, v___x_1373_);
lean_ctor_set(v___x_1400_, 0, v___x_1402_);
v___x_1404_ = v___x_1400_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_nextMacroScope_1391_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_ngen_1392_);
lean_ctor_set(v_reuseFailAlloc_1457_, 3, v_auxDeclNGen_1393_);
lean_ctor_set(v_reuseFailAlloc_1457_, 4, v_traceState_1394_);
lean_ctor_set(v_reuseFailAlloc_1457_, 5, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1457_, 6, v_recordedDeps_1395_);
lean_ctor_set(v_reuseFailAlloc_1457_, 7, v_messages_1396_);
lean_ctor_set(v_reuseFailAlloc_1457_, 8, v_infoState_1397_);
lean_ctor_set(v_reuseFailAlloc_1457_, 9, v_snapshotTasks_1398_);
v___x_1404_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v_mctx_1407_; lean_object* v_zetaDeltaFVarIds_1408_; lean_object* v_postponed_1409_; lean_object* v_diag_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1455_; 
v___x_1405_ = lean_st_ref_put(v___y_1304_, v___x_1404_);
v___x_1406_ = lean_st_ref_take(v___y_1302_);
v_mctx_1407_ = lean_ctor_get(v___x_1406_, 0);
v_zetaDeltaFVarIds_1408_ = lean_ctor_get(v___x_1406_, 2);
v_postponed_1409_ = lean_ctor_get(v___x_1406_, 3);
v_diag_1410_ = lean_ctor_get(v___x_1406_, 4);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1455_ == 0)
{
lean_object* v_unused_1456_; 
v_unused_1456_ = lean_ctor_get(v___x_1406_, 1);
lean_dec(v_unused_1456_);
v___x_1412_ = v___x_1406_;
v_isShared_1413_ = v_isSharedCheck_1455_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_diag_1410_);
lean_inc(v_postponed_1409_);
lean_inc(v_zetaDeltaFVarIds_1408_);
lean_inc(v_mctx_1407_);
lean_dec(v___x_1406_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1455_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 1, v___x_1385_);
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_mctx_1407_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v_zetaDeltaFVarIds_1408_);
lean_ctor_set(v_reuseFailAlloc_1454_, 3, v_postponed_1409_);
lean_ctor_set(v_reuseFailAlloc_1454_, 4, v_diag_1410_);
v___x_1415_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v_env_1418_; uint8_t v___x_1419_; 
v___x_1416_ = lean_st_ref_put(v___y_1302_, v___x_1415_);
v___x_1417_ = lean_st_ref_get(v___y_1304_);
v_env_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc_ref(v_env_1418_);
lean_dec(v___x_1417_);
lean_inc(v_indName_1300_);
v___x_1419_ = l_Lean_isMarkedMeta(v_env_1418_, v_indName_1300_);
if (v___x_1419_ == 0)
{
v___y_1338_ = v___y_1301_;
v___y_1339_ = v___y_1302_;
v___y_1340_ = v___y_1303_;
v___y_1341_ = v___y_1304_;
goto v___jp_1337_;
}
else
{
lean_object* v___x_1420_; lean_object* v_env_1421_; lean_object* v_nextMacroScope_1422_; lean_object* v_ngen_1423_; lean_object* v_auxDeclNGen_1424_; lean_object* v_traceState_1425_; lean_object* v_recordedDeps_1426_; lean_object* v_messages_1427_; lean_object* v_infoState_1428_; lean_object* v_snapshotTasks_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1452_; 
v___x_1420_ = lean_st_ref_take(v___y_1304_);
v_env_1421_ = lean_ctor_get(v___x_1420_, 0);
v_nextMacroScope_1422_ = lean_ctor_get(v___x_1420_, 1);
v_ngen_1423_ = lean_ctor_get(v___x_1420_, 2);
v_auxDeclNGen_1424_ = lean_ctor_get(v___x_1420_, 3);
v_traceState_1425_ = lean_ctor_get(v___x_1420_, 4);
v_recordedDeps_1426_ = lean_ctor_get(v___x_1420_, 6);
v_messages_1427_ = lean_ctor_get(v___x_1420_, 7);
v_infoState_1428_ = lean_ctor_get(v___x_1420_, 8);
v_snapshotTasks_1429_ = lean_ctor_get(v___x_1420_, 9);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1452_ == 0)
{
lean_object* v_unused_1453_; 
v_unused_1453_ = lean_ctor_get(v___x_1420_, 5);
lean_dec(v_unused_1453_);
v___x_1431_ = v___x_1420_;
v_isShared_1432_ = v_isSharedCheck_1452_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_snapshotTasks_1429_);
lean_inc(v_infoState_1428_);
lean_inc(v_messages_1427_);
lean_inc(v_recordedDeps_1426_);
lean_inc(v_traceState_1425_);
lean_inc(v_auxDeclNGen_1424_);
lean_inc(v_ngen_1423_);
lean_inc(v_nextMacroScope_1422_);
lean_inc(v_env_1421_);
lean_dec(v___x_1420_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1452_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v___x_1435_; 
lean_inc(v___x_1298_);
v___x_1433_ = l_Lean_markMeta(v_env_1421_, v___x_1298_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 5, v___x_1373_);
lean_ctor_set(v___x_1431_, 0, v___x_1433_);
v___x_1435_ = v___x_1431_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_nextMacroScope_1422_);
lean_ctor_set(v_reuseFailAlloc_1451_, 2, v_ngen_1423_);
lean_ctor_set(v_reuseFailAlloc_1451_, 3, v_auxDeclNGen_1424_);
lean_ctor_set(v_reuseFailAlloc_1451_, 4, v_traceState_1425_);
lean_ctor_set(v_reuseFailAlloc_1451_, 5, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1451_, 6, v_recordedDeps_1426_);
lean_ctor_set(v_reuseFailAlloc_1451_, 7, v_messages_1427_);
lean_ctor_set(v_reuseFailAlloc_1451_, 8, v_infoState_1428_);
lean_ctor_set(v_reuseFailAlloc_1451_, 9, v_snapshotTasks_1429_);
v___x_1435_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v_mctx_1438_; lean_object* v_zetaDeltaFVarIds_1439_; lean_object* v_postponed_1440_; lean_object* v_diag_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1449_; 
v___x_1436_ = lean_st_ref_put(v___y_1304_, v___x_1435_);
v___x_1437_ = lean_st_ref_take(v___y_1302_);
v_mctx_1438_ = lean_ctor_get(v___x_1437_, 0);
v_zetaDeltaFVarIds_1439_ = lean_ctor_get(v___x_1437_, 2);
v_postponed_1440_ = lean_ctor_get(v___x_1437_, 3);
v_diag_1441_ = lean_ctor_get(v___x_1437_, 4);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1449_ == 0)
{
lean_object* v_unused_1450_; 
v_unused_1450_ = lean_ctor_get(v___x_1437_, 1);
lean_dec(v_unused_1450_);
v___x_1443_ = v___x_1437_;
v_isShared_1444_ = v_isSharedCheck_1449_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_diag_1441_);
lean_inc(v_postponed_1440_);
lean_inc(v_zetaDeltaFVarIds_1439_);
lean_inc(v_mctx_1438_);
lean_dec(v___x_1437_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1449_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 1, v___x_1385_);
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_mctx_1438_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1448_, 2, v_zetaDeltaFVarIds_1439_);
lean_ctor_set(v_reuseFailAlloc_1448_, 3, v_postponed_1440_);
lean_ctor_set(v_reuseFailAlloc_1448_, 4, v_diag_1441_);
v___x_1446_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_st_ref_put(v___y_1302_, v___x_1446_);
v___y_1338_ = v___y_1301_;
v___y_1339_ = v___y_1302_;
v___y_1340_ = v___y_1303_;
v___y_1341_ = v___y_1304_;
goto v___jp_1337_;
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
lean_dec_ref(v___x_1331_);
lean_dec(v_a_1314_);
lean_dec(v_indName_1300_);
lean_dec(v_levelParams_1299_);
lean_dec(v___x_1298_);
lean_dec_ref(v_val_1291_);
return v___x_1358_;
}
v___jp_1332_:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lean_compileDecl(v___x_1331_, v___x_1290_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v___x_1336_; 
lean_dec_ref_known(v___x_1335_, 1);
v___x_1336_ = l_Lean_enableRealizationsForConst(v___x_1298_, v___y_1333_, v___y_1334_);
return v___x_1336_;
}
else
{
lean_dec(v___x_1298_);
return v___x_1335_;
}
}
v___jp_1337_:
{
lean_object* v___x_1342_; uint8_t v___x_1343_; 
v___x_1342_ = l_Lean_InductiveVal_numCtors(v_val_1291_);
lean_dec_ref(v_val_1291_);
v___x_1343_ = lean_nat_dec_eq(v___x_1342_, v___x_1321_);
lean_dec(v___x_1342_);
if (v___x_1343_ == 0)
{
uint8_t v___x_1344_; 
v___x_1344_ = l_Lean_Compiler_LCNF_isRuntimeBuiltinType(v_indName_1300_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; 
v___x_1345_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl(v_indName_1300_, v_levelParams_1299_, v_a_1314_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1347_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
lean_inc(v___x_1298_);
v___x_1347_ = l_Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9(v___x_1298_, v_a_1346_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_dec_ref_known(v___x_1347_, 1);
v___y_1333_ = v___y_1340_;
v___y_1334_ = v___y_1341_;
goto v___jp_1332_;
}
else
{
lean_dec_ref(v___x_1331_);
lean_dec(v___x_1298_);
return v___x_1347_;
}
}
else
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1355_; 
lean_dec_ref(v___x_1331_);
lean_dec(v___x_1298_);
v_a_1348_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1350_ = v___x_1345_;
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1345_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1355_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1348_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
else
{
lean_dec(v_a_1314_);
lean_dec(v_indName_1300_);
lean_dec(v_levelParams_1299_);
v___y_1333_ = v___y_1340_;
v___y_1334_ = v___y_1341_;
goto v___jp_1332_;
}
}
else
{
uint8_t v___x_1356_; lean_object* v___x_1357_; 
lean_dec(v_a_1314_);
lean_dec(v_indName_1300_);
lean_dec(v_levelParams_1299_);
v___x_1356_ = 2;
lean_inc(v___x_1298_);
v___x_1357_ = l_Lean_Meta_setInlineAttribute(v___x_1298_, v___x_1356_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_dec_ref_known(v___x_1357_, 1);
v___y_1333_ = v___y_1340_;
v___y_1334_ = v___y_1341_;
goto v___jp_1332_;
}
else
{
lean_dec_ref(v___x_1331_);
lean_dec(v___x_1298_);
return v___x_1357_;
}
}
}
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec(v_a_1314_);
lean_dec(v_indName_1300_);
lean_dec(v_levelParams_1299_);
lean_dec(v___x_1298_);
lean_dec_ref(v_val_1291_);
v_a_1468_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1316_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1316_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_dec_ref(v___f_1312_);
lean_dec(v_indName_1300_);
lean_dec(v_levelParams_1299_);
lean_dec(v___x_1298_);
lean_dec_ref(v_val_1291_);
lean_dec_ref(v___x_1286_);
v_a_1476_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1313_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1313_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec(v_indName_1300_);
lean_dec(v_levelParams_1299_);
lean_dec(v___x_1298_);
lean_dec(v___x_1297_);
lean_dec(v_ctors_1296_);
lean_dec_ref(v___x_1295_);
lean_dec(v___x_1294_);
lean_dec(v___x_1293_);
lean_dec_ref(v___x_1292_);
lean_dec_ref(v_val_1291_);
lean_dec_ref(v_xs_1288_);
lean_dec_ref(v___x_1287_);
lean_dec_ref(v___x_1286_);
v_a_1484_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1306_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1306_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1___boxed(lean_object** _args){
lean_object* v___x_1492_ = _args[0];
lean_object* v___x_1493_ = _args[1];
lean_object* v_xs_1494_ = _args[2];
lean_object* v___x_1495_ = _args[3];
lean_object* v___x_1496_ = _args[4];
lean_object* v_val_1497_ = _args[5];
lean_object* v___x_1498_ = _args[6];
lean_object* v___x_1499_ = _args[7];
lean_object* v___x_1500_ = _args[8];
lean_object* v___x_1501_ = _args[9];
lean_object* v_ctors_1502_ = _args[10];
lean_object* v___x_1503_ = _args[11];
lean_object* v___x_1504_ = _args[12];
lean_object* v_levelParams_1505_ = _args[13];
lean_object* v_indName_1506_ = _args[14];
lean_object* v___y_1507_ = _args[15];
lean_object* v___y_1508_ = _args[16];
lean_object* v___y_1509_ = _args[17];
lean_object* v___y_1510_ = _args[18];
lean_object* v___y_1511_ = _args[19];
_start:
{
uint8_t v___x_21084__boxed_1512_; uint8_t v___x_21085__boxed_1513_; lean_object* v_res_1514_; 
v___x_21084__boxed_1512_ = lean_unbox(v___x_1495_);
v___x_21085__boxed_1513_ = lean_unbox(v___x_1496_);
v_res_1514_ = l_Lean_mkCtorIdx___lam__1(v___x_1492_, v___x_1493_, v_xs_1494_, v___x_21084__boxed_1512_, v___x_21085__boxed_1513_, v_val_1497_, v___x_1498_, v___x_1499_, v___x_1500_, v___x_1501_, v_ctors_1502_, v___x_1503_, v___x_1504_, v_levelParams_1505_, v_indName_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15(size_t v_sz_1515_, size_t v_i_1516_, lean_object* v_bs_1517_){
_start:
{
uint8_t v___x_1518_; 
v___x_1518_ = lean_usize_dec_lt(v_i_1516_, v_sz_1515_);
if (v___x_1518_ == 0)
{
return v_bs_1517_;
}
else
{
lean_object* v_v_1519_; lean_object* v___x_1520_; lean_object* v_bs_x27_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; size_t v___x_1526_; size_t v___x_1527_; lean_object* v___x_1528_; 
v_v_1519_ = lean_array_uget(v_bs_1517_, v_i_1516_);
v___x_1520_ = lean_unsigned_to_nat(0u);
v_bs_x27_1521_ = lean_array_uset(v_bs_1517_, v_i_1516_, v___x_1520_);
v___x_1522_ = l_Lean_Expr_fvarId_x21(v_v_1519_);
lean_dec(v_v_1519_);
v___x_1523_ = 1;
v___x_1524_ = lean_box(v___x_1523_);
v___x_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1522_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = ((size_t)1ULL);
v___x_1527_ = lean_usize_add(v_i_1516_, v___x_1526_);
v___x_1528_ = lean_array_uset(v_bs_x27_1521_, v_i_1516_, v___x_1525_);
v_i_1516_ = v___x_1527_;
v_bs_1517_ = v___x_1528_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15___boxed(lean_object* v_sz_1530_, lean_object* v_i_1531_, lean_object* v_bs_1532_){
_start:
{
size_t v_sz_boxed_1533_; size_t v_i_boxed_1534_; lean_object* v_res_1535_; 
v_sz_boxed_1533_ = lean_unbox_usize(v_sz_1530_);
lean_dec(v_sz_1530_);
v_i_boxed_1534_ = lean_unbox_usize(v_i_1531_);
lean_dec(v_i_1531_);
v_res_1535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15(v_sz_boxed_1533_, v_i_boxed_1534_, v_bs_1532_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(lean_object* v_bs_1536_, lean_object* v_k_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1536_, v_k_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1551_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1546_ = v___x_1543_;
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1551_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1549_; 
if (v_isShared_1547_ == 0)
{
v___x_1549_ = v___x_1546_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v_a_1544_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
v_a_1552_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1543_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1543_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg___boxed(lean_object* v_bs_1560_, lean_object* v_k_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(v_bs_1560_, v_k_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec_ref(v_bs_1560_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(lean_object* v_bs_1568_, lean_object* v_k_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
size_t v_sz_1575_; size_t v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v_sz_1575_ = lean_array_size(v_bs_1568_);
v___x_1576_ = ((size_t)0ULL);
v___x_1577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__15(v_sz_1575_, v___x_1576_, v_bs_1568_);
v___x_1578_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(v___x_1577_, v_k_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec_ref(v___x_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg___boxed(lean_object* v_bs_1579_, lean_object* v_k_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(v_bs_1579_, v_k_1580_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_);
lean_dec(v___y_1584_);
lean_dec_ref(v___y_1583_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2(lean_object* v_numParams_1590_, lean_object* v_indName_1591_, lean_object* v___x_1592_, lean_object* v___x_1593_, uint8_t v___x_1594_, uint8_t v___x_1595_, lean_object* v_val_1596_, lean_object* v___x_1597_, lean_object* v_ctors_1598_, lean_object* v___x_1599_, lean_object* v_levelParams_1600_, lean_object* v_xs_1601_, lean_object* v_x_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___f_1620_; lean_object* v___x_1621_; 
v___x_1608_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1590_);
lean_inc_ref_n(v_xs_1601_, 3);
v___x_1609_ = l_Array_toSubarray___redArg(v_xs_1601_, v___x_1608_, v_numParams_1590_);
v___x_1610_ = l_Subarray_copy___redArg(v___x_1609_);
v___x_1611_ = lean_array_get_size(v_xs_1601_);
v___x_1612_ = l_Array_toSubarray___redArg(v_xs_1601_, v_numParams_1590_, v___x_1611_);
v___x_1613_ = l_Subarray_copy___redArg(v___x_1612_);
lean_inc(v___x_1592_);
lean_inc(v_indName_1591_);
v___x_1614_ = l_Lean_mkConst(v_indName_1591_, v___x_1592_);
v___x_1615_ = l_Lean_mkAppN(v___x_1614_, v_xs_1601_);
v___x_1616_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__2___closed__1));
v___x_1617_ = l_Lean_mkConst(v___x_1616_, v___x_1593_);
v___x_1618_ = lean_box(v___x_1594_);
v___x_1619_ = lean_box(v___x_1595_);
v___f_1620_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__1___boxed), 20, 15);
lean_closure_set(v___f_1620_, 0, v___x_1615_);
lean_closure_set(v___f_1620_, 1, v___x_1617_);
lean_closure_set(v___f_1620_, 2, v_xs_1601_);
lean_closure_set(v___f_1620_, 3, v___x_1618_);
lean_closure_set(v___f_1620_, 4, v___x_1619_);
lean_closure_set(v___f_1620_, 5, v_val_1596_);
lean_closure_set(v___f_1620_, 6, v___x_1613_);
lean_closure_set(v___f_1620_, 7, v___x_1592_);
lean_closure_set(v___f_1620_, 8, v___x_1597_);
lean_closure_set(v___f_1620_, 9, v___x_1610_);
lean_closure_set(v___f_1620_, 10, v_ctors_1598_);
lean_closure_set(v___f_1620_, 11, v___x_1608_);
lean_closure_set(v___f_1620_, 12, v___x_1599_);
lean_closure_set(v___f_1620_, 13, v_levelParams_1600_);
lean_closure_set(v___f_1620_, 14, v_indName_1591_);
v___x_1621_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(v_xs_1601_, v___f_1620_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2___boxed(lean_object** _args){
lean_object* v_numParams_1622_ = _args[0];
lean_object* v_indName_1623_ = _args[1];
lean_object* v___x_1624_ = _args[2];
lean_object* v___x_1625_ = _args[3];
lean_object* v___x_1626_ = _args[4];
lean_object* v___x_1627_ = _args[5];
lean_object* v_val_1628_ = _args[6];
lean_object* v___x_1629_ = _args[7];
lean_object* v_ctors_1630_ = _args[8];
lean_object* v___x_1631_ = _args[9];
lean_object* v_levelParams_1632_ = _args[10];
lean_object* v_xs_1633_ = _args[11];
lean_object* v_x_1634_ = _args[12];
lean_object* v___y_1635_ = _args[13];
lean_object* v___y_1636_ = _args[14];
lean_object* v___y_1637_ = _args[15];
lean_object* v___y_1638_ = _args[16];
lean_object* v___y_1639_ = _args[17];
_start:
{
uint8_t v___x_21530__boxed_1640_; uint8_t v___x_21531__boxed_1641_; lean_object* v_res_1642_; 
v___x_21530__boxed_1640_ = lean_unbox(v___x_1626_);
v___x_21531__boxed_1641_ = lean_unbox(v___x_1627_);
v_res_1642_ = l_Lean_mkCtorIdx___lam__2(v_numParams_1622_, v_indName_1623_, v___x_1624_, v___x_1625_, v___x_21530__boxed_1640_, v___x_21531__boxed_1641_, v_val_1628_, v___x_1629_, v_ctors_1630_, v___x_1631_, v_levelParams_1632_, v_xs_1633_, v_x_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec_ref(v_x_1634_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(lean_object* v_a_1643_, lean_object* v_a_1644_){
_start:
{
if (lean_obj_tag(v_a_1643_) == 0)
{
lean_object* v___x_1645_; 
v___x_1645_ = l_List_reverse___redArg(v_a_1644_);
return v___x_1645_;
}
else
{
lean_object* v_head_1646_; lean_object* v_tail_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1656_; 
v_head_1646_ = lean_ctor_get(v_a_1643_, 0);
v_tail_1647_ = lean_ctor_get(v_a_1643_, 1);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_a_1643_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1649_ = v_a_1643_;
v_isShared_1650_ = v_isSharedCheck_1656_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_tail_1647_);
lean_inc(v_head_1646_);
lean_dec(v_a_1643_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1656_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1651_ = l_Lean_mkLevelParam(v_head_1646_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 1, v_a_1644_);
lean_ctor_set(v___x_1649_, 0, v___x_1651_);
v___x_1653_ = v___x_1649_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1651_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_a_1644_);
v___x_1653_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
v_a_1643_ = v_tail_1647_;
v_a_1644_ = v___x_1653_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg(lean_object* v_ref_1657_, lean_object* v_msg_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_toCold_1664_; lean_object* v_currRecDepth_1665_; lean_object* v_ref_1666_; uint16_t v_optionFlags_1667_; uint8_t v_suppressElabErrors_1668_; uint8_t v_isRecordingDeps_1669_; lean_object* v_ref_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v_toCold_1664_ = lean_ctor_get(v___y_1661_, 0);
v_currRecDepth_1665_ = lean_ctor_get(v___y_1661_, 1);
v_ref_1666_ = lean_ctor_get(v___y_1661_, 2);
v_optionFlags_1667_ = lean_ctor_get_uint16(v___y_1661_, sizeof(void*)*3);
v_suppressElabErrors_1668_ = lean_ctor_get_uint8(v___y_1661_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1669_ = lean_ctor_get_uint8(v___y_1661_, sizeof(void*)*3 + 3);
v_ref_1670_ = l_Lean_replaceRef(v_ref_1657_, v_ref_1666_);
lean_inc(v_currRecDepth_1665_);
lean_inc_ref(v_toCold_1664_);
v___x_1671_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1671_, 0, v_toCold_1664_);
lean_ctor_set(v___x_1671_, 1, v_currRecDepth_1665_);
lean_ctor_set(v___x_1671_, 2, v_ref_1670_);
lean_ctor_set_uint16(v___x_1671_, sizeof(void*)*3, v_optionFlags_1667_);
lean_ctor_set_uint8(v___x_1671_, sizeof(void*)*3 + 2, v_suppressElabErrors_1668_);
lean_ctor_set_uint8(v___x_1671_, sizeof(void*)*3 + 3, v_isRecordingDeps_1669_);
v___x_1672_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_1658_, v___y_1659_, v___y_1660_, v___x_1671_, v___y_1662_);
lean_dec_ref_known(v___x_1671_, 3);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg___boxed(lean_object* v_ref_1673_, lean_object* v_msg_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg(v_ref_1673_, v_msg_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v_ref_1673_);
return v_res_1680_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = lean_obj_once(&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1, &l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1_once, _init_l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_mkCtorIdxImpl___closed__1);
v___x_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1681_);
return v___x_1682_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__1(void){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1683_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1684_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0);
v___x_1685_ = lean_unsigned_to_nat(0u);
v___x_1686_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
lean_ctor_set(v___x_1686_, 2, v___x_1685_);
lean_ctor_set(v___x_1686_, 3, v___x_1685_);
lean_ctor_set(v___x_1686_, 4, v___x_1684_);
lean_ctor_set(v___x_1686_, 5, v___x_1684_);
lean_ctor_set(v___x_1686_, 6, v___x_1684_);
lean_ctor_set(v___x_1686_, 7, v___x_1684_);
lean_ctor_set(v___x_1686_, 8, v___x_1684_);
lean_ctor_set(v___x_1686_, 9, v___x_1684_);
lean_ctor_set(v___x_1686_, 10, v___x_1684_);
lean_ctor_set(v___x_1686_, 11, v___x_1683_);
return v___x_1686_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = lean_unsigned_to_nat(32u);
v___x_1688_ = lean_mk_empty_array_with_capacity(v___x_1687_);
v___x_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
return v___x_1689_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__3(void){
_start:
{
size_t v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1690_ = ((size_t)5ULL);
v___x_1691_ = lean_unsigned_to_nat(0u);
v___x_1692_ = lean_unsigned_to_nat(32u);
v___x_1693_ = lean_mk_empty_array_with_capacity(v___x_1692_);
v___x_1694_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__2);
v___x_1695_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
lean_ctor_set(v___x_1695_, 1, v___x_1693_);
lean_ctor_set(v___x_1695_, 2, v___x_1691_);
lean_ctor_set(v___x_1695_, 3, v___x_1691_);
lean_ctor_set_usize(v___x_1695_, 4, v___x_1690_);
return v___x_1695_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__4(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1696_ = lean_box(1);
v___x_1697_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__3);
v___x_1698_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__0);
v___x_1699_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
lean_ctor_set(v___x_1699_, 1, v___x_1697_);
lean_ctor_set(v___x_1699_, 2, v___x_1696_);
return v___x_1699_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6(void){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__5));
v___x_1702_ = l_Lean_stringToMessageData(v___x_1701_);
return v___x_1702_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__8(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__7));
v___x_1705_ = l_Lean_stringToMessageData(v___x_1704_);
return v___x_1705_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__10(void){
_start:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__9));
v___x_1708_ = l_Lean_stringToMessageData(v___x_1707_);
return v___x_1708_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__12(void){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1710_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__11));
v___x_1711_ = l_Lean_stringToMessageData(v___x_1710_);
return v___x_1711_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__14(void){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__13));
v___x_1714_ = l_Lean_stringToMessageData(v___x_1713_);
return v___x_1714_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__15));
v___x_1717_ = l_Lean_stringToMessageData(v___x_1716_);
return v___x_1717_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__17));
v___x_1720_ = l_Lean_stringToMessageData(v___x_1719_);
return v___x_1720_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__20(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__19));
v___x_1723_ = l_Lean_stringToMessageData(v___x_1722_);
return v___x_1723_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__22(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__21));
v___x_1726_ = l_Lean_stringToMessageData(v___x_1725_);
return v___x_1726_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__24(void){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__23));
v___x_1729_ = l_Lean_stringToMessageData(v___x_1728_);
return v___x_1729_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__26(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__25));
v___x_1732_ = l_Lean_stringToMessageData(v___x_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg(lean_object* v_msg_1733_, lean_object* v_declHint_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v_env_1739_; uint8_t v___x_1740_; 
v___x_1737_ = lean_box(0);
v___x_1738_ = lean_st_ref_get(v___y_1735_);
v_env_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc_ref(v_env_1739_);
lean_dec(v___x_1738_);
v___x_1740_ = l_Lean_Name_isAnonymous(v_declHint_1734_);
if (v___x_1740_ == 0)
{
uint8_t v_isExporting_1741_; 
v_isExporting_1741_ = lean_ctor_get_uint8(v_env_1739_, sizeof(void*)*13);
if (v_isExporting_1741_ == 0)
{
lean_object* v___x_1742_; 
lean_dec_ref(v_env_1739_);
lean_dec(v_declHint_1734_);
v___x_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1742_, 0, v_msg_1733_);
return v___x_1742_;
}
else
{
lean_object* v___x_1743_; uint8_t v___x_1744_; 
lean_inc_ref(v_env_1739_);
v___x_1743_ = l_Lean_Environment_setExporting(v_env_1739_, v___x_1740_);
lean_inc(v_declHint_1734_);
lean_inc_ref(v___x_1743_);
v___x_1744_ = l_Lean_Environment_contains(v___x_1743_, v_declHint_1734_, v_isExporting_1741_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; 
lean_dec_ref(v___x_1743_);
lean_dec_ref(v_env_1739_);
lean_dec(v_declHint_1734_);
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_msg_1733_);
return v___x_1745_;
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v_c_1751_; lean_object* v___x_1752_; 
v___x_1746_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__1);
v___x_1747_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__4);
v___x_1748_ = l_Lean_Options_empty;
v___x_1749_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1743_);
lean_ctor_set(v___x_1749_, 1, v___x_1746_);
lean_ctor_set(v___x_1749_, 2, v___x_1747_);
lean_ctor_set(v___x_1749_, 3, v___x_1748_);
lean_inc(v_declHint_1734_);
v___x_1750_ = l_Lean_MessageData_ofConstName(v_declHint_1734_, v___x_1740_);
v_c_1751_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1751_, 0, v___x_1749_);
lean_ctor_set(v_c_1751_, 1, v___x_1750_);
v___x_1752_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1739_, v_declHint_1734_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
lean_dec_ref(v_env_1739_);
lean_dec(v_declHint_1734_);
v___x_1753_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6);
v___x_1754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
lean_ctor_set(v___x_1754_, 1, v_c_1751_);
v___x_1755_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__8);
v___x_1756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1754_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = l_Lean_MessageData_note(v___x_1756_);
v___x_1758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1758_, 0, v_msg_1733_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
return v___x_1759_;
}
else
{
lean_object* v_val_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1816_; 
v_val_1760_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1762_ = v___x_1752_;
v_isShared_1763_ = v_isSharedCheck_1816_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_val_1760_);
lean_dec(v___x_1752_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1816_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; lean_object* v_modules_1765_; lean_object* v_moduleNames_1766_; lean_object* v_mod_1767_; uint8_t v___y_1769_; uint8_t v___x_1799_; 
v___x_1764_ = l_Lean_Environment_header(v_env_1739_);
lean_dec_ref(v_env_1739_);
v_modules_1765_ = lean_ctor_get(v___x_1764_, 3);
lean_inc_ref(v_modules_1765_);
v_moduleNames_1766_ = lean_ctor_get(v___x_1764_, 4);
lean_inc_ref(v_moduleNames_1766_);
lean_dec_ref(v___x_1764_);
v_mod_1767_ = lean_array_get(v___x_1737_, v_moduleNames_1766_, v_val_1760_);
lean_dec_ref(v_moduleNames_1766_);
v___x_1799_ = l_Lean_isPrivateName(v_declHint_1734_);
lean_dec(v_declHint_1734_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; uint8_t v___x_1801_; 
v___x_1800_ = lean_array_get_size(v_modules_1765_);
v___x_1801_ = lean_nat_dec_lt(v_val_1760_, v___x_1800_);
if (v___x_1801_ == 0)
{
lean_dec_ref(v_modules_1765_);
lean_dec(v_val_1760_);
v___y_1769_ = v___x_1799_;
goto v___jp_1768_;
}
else
{
lean_object* v___x_1802_; lean_object* v_toImport_1803_; uint8_t v_isExported_1804_; 
v___x_1802_ = lean_array_fget(v_modules_1765_, v_val_1760_);
lean_dec(v_val_1760_);
lean_dec_ref(v_modules_1765_);
v_toImport_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc_ref(v_toImport_1803_);
lean_dec(v___x_1802_);
v_isExported_1804_ = lean_ctor_get_uint8(v_toImport_1803_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1803_);
v___y_1769_ = v_isExported_1804_;
goto v___jp_1768_;
}
}
else
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
lean_dec_ref(v_modules_1765_);
lean_del_object(v___x_1762_);
lean_dec(v_val_1760_);
v___x_1805_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__6);
v___x_1806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
lean_ctor_set(v___x_1806_, 1, v_c_1751_);
v___x_1807_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__24);
v___x_1808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1806_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = l_Lean_MessageData_ofName(v_mod_1767_);
v___x_1810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1808_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__26, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__26_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__26);
v___x_1812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1810_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = l_Lean_MessageData_note(v___x_1812_);
v___x_1814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1814_, 0, v_msg_1733_);
lean_ctor_set(v___x_1814_, 1, v___x_1813_);
v___x_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
return v___x_1815_;
}
v___jp_1768_:
{
if (v___y_1769_ == 0)
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1770_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__10);
v___x_1771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
lean_ctor_set(v___x_1771_, 1, v_c_1751_);
v___x_1772_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__12);
v___x_1773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1771_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v___x_1774_ = l_Lean_MessageData_ofName(v_mod_1767_);
v___x_1775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1773_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__14);
v___x_1777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1775_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = l_Lean_MessageData_note(v___x_1777_);
v___x_1779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1779_, 0, v_msg_1733_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set_tag(v___x_1762_, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1779_);
v___x_1781_ = v___x_1762_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
else
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1797_; 
v___x_1783_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__16);
v___x_1784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
lean_ctor_set(v___x_1784_, 1, v_c_1751_);
v___x_1785_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__18);
v___x_1786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1784_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = l_Lean_MessageData_ofName(v_mod_1767_);
lean_inc_ref(v___x_1787_);
v___x_1788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1786_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__20);
v___x_1790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1788_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
v___x_1791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
lean_ctor_set(v___x_1791_, 1, v___x_1787_);
v___x_1792_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___closed__22);
v___x_1793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1791_);
lean_ctor_set(v___x_1793_, 1, v___x_1792_);
v___x_1794_ = l_Lean_MessageData_note(v___x_1793_);
v___x_1795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1795_, 0, v_msg_1733_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set_tag(v___x_1762_, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1795_);
v___x_1797_ = v___x_1762_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
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
lean_object* v___x_1817_; 
lean_dec_ref(v_env_1739_);
lean_dec(v_declHint_1734_);
v___x_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1817_, 0, v_msg_1733_);
return v___x_1817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg___boxed(lean_object* v_msg_1818_, lean_object* v_declHint_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg(v_msg_1818_, v_declHint_1819_, v___y_1820_);
lean_dec(v___y_1820_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22(lean_object* v_msg_1823_, lean_object* v_declHint_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v___x_1830_; lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1840_; 
v___x_1830_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg(v_msg_1823_, v_declHint_1824_, v___y_1828_);
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1833_ = v___x_1830_;
v_isShared_1834_ = v_isSharedCheck_1840_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1830_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1840_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1835_ = l_Lean_unknownIdentifierMessageTag;
v___x_1836_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
lean_ctor_set(v___x_1836_, 1, v_a_1831_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1836_);
v___x_1838_ = v___x_1833_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22___boxed(lean_object* v_msg_1841_, lean_object* v_declHint_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22(v_msg_1841_, v_declHint_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg(lean_object* v_ref_1849_, lean_object* v_msg_1850_, lean_object* v_declHint_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v___x_1857_; lean_object* v_a_1858_; lean_object* v___x_1859_; 
v___x_1857_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22(v_msg_1850_, v_declHint_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_a_1858_);
lean_dec_ref(v___x_1857_);
v___x_1859_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg(v_ref_1849_, v_a_1858_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg___boxed(lean_object* v_ref_1860_, lean_object* v_msg_1861_, lean_object* v_declHint_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg(v_ref_1860_, v_msg_1861_, v_declHint_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v_ref_1860_);
return v_res_1868_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0));
v___x_1871_ = l_Lean_stringToMessageData(v___x_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(lean_object* v_ref_1872_, lean_object* v_constName_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___x_1879_; uint8_t v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1879_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1);
v___x_1880_ = 0;
lean_inc(v_constName_1873_);
v___x_1881_ = l_Lean_MessageData_ofConstName(v_constName_1873_, v___x_1880_);
v___x_1882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1879_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1);
v___x_1884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1882_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg(v_ref_1872_, v___x_1884_, v_constName_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1886_, lean_object* v_constName_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1886_, v_constName_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v_ref_1886_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(lean_object* v_constName_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_ref_1900_; lean_object* v___x_1901_; 
v_ref_1900_ = lean_ctor_get(v___y_1897_, 2);
v___x_1901_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1900_, v_constName_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg___boxed(lean_object* v_constName_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(lean_object* v_constName_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v___x_1915_; lean_object* v_env_1916_; uint8_t v___x_1917_; lean_object* v___x_1918_; 
v___x_1915_ = lean_st_ref_get(v___y_1913_);
v_env_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc_ref(v_env_1916_);
lean_dec(v___x_1915_);
v___x_1917_ = 0;
lean_inc(v_constName_1909_);
v___x_1918_ = l_Lean_Environment_find_x3f(v_env_1916_, v_constName_1909_, v___x_1917_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v___x_1919_; 
v___x_1919_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
return v___x_1919_;
}
else
{
lean_object* v_val_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec(v_constName_1909_);
v_val_1920_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1918_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_val_1920_);
lean_dec(v___x_1918_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
lean_ctor_set_tag(v___x_1922_, 0);
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_val_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2___boxed(lean_object* v_constName_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_constName_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
return v_res_1934_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1937_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6));
v___x_1938_ = lean_unsigned_to_nat(62u);
v___x_1939_ = lean_unsigned_to_nat(83u);
v___x_1940_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__3___closed__1));
v___x_1941_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__3___closed__0));
v___x_1942_ = l_mkPanicMessageWithDecl(v___x_1941_, v___x_1940_, v___x_1939_, v___x_1938_, v___x_1937_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3(lean_object* v_indName_1943_, uint8_t v___x_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v___x_1950_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1947_);
v___x_1951_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_genCtorIdx;
v___x_1952_ = l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(v___x_1950_, v___x_1951_);
lean_dec_ref(v___x_1950_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
lean_dec(v_indName_1943_);
v___x_1953_ = lean_box(0);
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
return v___x_1954_;
}
else
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_2041_; 
lean_inc(v_indName_1943_);
v___x_1955_ = l_Lean_mkCtorIdxName(v_indName_1943_);
lean_inc(v___x_1955_);
v___x_1956_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v___x_1955_, v___x_1952_, v___y_1948_);
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_1959_ = v___x_1956_;
v_isShared_1960_ = v_isSharedCheck_2041_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1956_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_2041_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
uint8_t v___x_1961_; 
v___x_1961_ = lean_unbox(v_a_1957_);
lean_dec(v_a_1957_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; 
lean_del_object(v___x_1959_);
lean_inc(v_indName_1943_);
v___x_1962_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_indName_1943_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1962_, 1);
if (lean_obj_tag(v_a_1963_) == 5)
{
lean_object* v_val_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_2026_; 
v_val_1964_ = lean_ctor_get(v_a_1963_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_a_1963_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_1966_ = v_a_1963_;
v_isShared_1967_ = v_isSharedCheck_2026_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_val_1964_);
lean_dec(v_a_1963_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_2026_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v_toConstantVal_1968_; lean_object* v_numParams_1969_; lean_object* v_numIndices_1970_; lean_object* v_ctors_1971_; lean_object* v_levelParams_1972_; lean_object* v_type_1973_; lean_object* v___x_1974_; 
v_toConstantVal_1968_ = lean_ctor_get(v_val_1964_, 0);
v_numParams_1969_ = lean_ctor_get(v_val_1964_, 1);
lean_inc(v_numParams_1969_);
v_numIndices_1970_ = lean_ctor_get(v_val_1964_, 2);
lean_inc(v_numIndices_1970_);
v_ctors_1971_ = lean_ctor_get(v_val_1964_, 4);
lean_inc(v_ctors_1971_);
v_levelParams_1972_ = lean_ctor_get(v_toConstantVal_1968_, 1);
lean_inc(v_levelParams_1972_);
v_type_1973_ = lean_ctor_get(v_toConstantVal_1968_, 2);
lean_inc_ref_n(v_type_1973_, 2);
v___x_1974_ = l_Lean_Meta_isPropFormerType(v_type_1973_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2017_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_2017_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2017_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
uint8_t v___x_1979_; 
v___x_1979_ = lean_unbox(v_a_1975_);
lean_dec(v_a_1975_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_del_object(v___x_1977_);
lean_inc(v_indName_1943_);
v___x_1980_ = l_Lean_mkCasesOnName(v_indName_1943_);
lean_inc(v___x_1980_);
v___x_1981_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v___x_1980_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2004_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_2004_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2004_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; uint8_t v___x_1989_; 
v___x_1986_ = l_List_lengthTR___redArg(v_levelParams_1972_);
v___x_1987_ = l_Lean_ConstantInfo_levelParams(v_a_1982_);
lean_dec(v_a_1982_);
v___x_1988_ = l_List_lengthTR___redArg(v___x_1987_);
lean_dec(v___x_1987_);
v___x_1989_ = lean_nat_dec_lt(v___x_1986_, v___x_1988_);
lean_dec(v___x_1988_);
lean_dec(v___x_1986_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1990_; lean_object* v___x_1992_; 
lean_dec(v___x_1980_);
lean_dec_ref(v_type_1973_);
lean_dec(v_levelParams_1972_);
lean_dec(v_ctors_1971_);
lean_dec(v_numIndices_1970_);
lean_dec(v_numParams_1969_);
lean_del_object(v___x_1966_);
lean_dec_ref(v_val_1964_);
lean_dec(v___x_1955_);
lean_dec(v_indName_1943_);
v___x_1990_ = lean_box(0);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1990_);
v___x_1992_ = v___x_1984_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
else
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___f_1998_; lean_object* v___x_1999_; lean_object* v___x_2001_; 
lean_del_object(v___x_1984_);
v___x_1994_ = lean_box(0);
lean_inc(v_levelParams_1972_);
v___x_1995_ = l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(v_levelParams_1972_, v___x_1994_);
v___x_1996_ = lean_box(v___x_1944_);
v___x_1997_ = lean_box(v___x_1952_);
lean_inc(v_numParams_1969_);
v___f_1998_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__2___boxed), 18, 11);
lean_closure_set(v___f_1998_, 0, v_numParams_1969_);
lean_closure_set(v___f_1998_, 1, v_indName_1943_);
lean_closure_set(v___f_1998_, 2, v___x_1995_);
lean_closure_set(v___f_1998_, 3, v___x_1994_);
lean_closure_set(v___f_1998_, 4, v___x_1996_);
lean_closure_set(v___f_1998_, 5, v___x_1997_);
lean_closure_set(v___f_1998_, 6, v_val_1964_);
lean_closure_set(v___f_1998_, 7, v___x_1980_);
lean_closure_set(v___f_1998_, 8, v_ctors_1971_);
lean_closure_set(v___f_1998_, 9, v___x_1955_);
lean_closure_set(v___f_1998_, 10, v_levelParams_1972_);
v___x_1999_ = lean_nat_add(v_numParams_1969_, v_numIndices_1970_);
lean_dec(v_numIndices_1970_);
lean_dec(v_numParams_1969_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set_tag(v___x_1966_, 1);
lean_ctor_set(v___x_1966_, 0, v___x_1999_);
v___x_2001_ = v___x_1966_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_1973_, v___x_2001_, v___f_1998_, v___x_1944_, v___x_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
return v___x_2002_;
}
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec(v___x_1980_);
lean_dec_ref(v_type_1973_);
lean_dec(v_levelParams_1972_);
lean_dec(v_ctors_1971_);
lean_dec(v_numIndices_1970_);
lean_dec(v_numParams_1969_);
lean_del_object(v___x_1966_);
lean_dec_ref(v_val_1964_);
lean_dec(v___x_1955_);
lean_dec(v_indName_1943_);
v_a_2005_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1981_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1981_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
else
{
lean_object* v___x_2013_; lean_object* v___x_2015_; 
lean_dec_ref(v_type_1973_);
lean_dec(v_levelParams_1972_);
lean_dec(v_ctors_1971_);
lean_dec(v_numIndices_1970_);
lean_dec(v_numParams_1969_);
lean_del_object(v___x_1966_);
lean_dec_ref(v_val_1964_);
lean_dec(v___x_1955_);
lean_dec(v_indName_1943_);
v___x_2013_ = lean_box(0);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_2013_);
v___x_2015_ = v___x_1977_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_dec_ref(v_type_1973_);
lean_dec(v_levelParams_1972_);
lean_dec(v_ctors_1971_);
lean_dec(v_numIndices_1970_);
lean_dec(v_numParams_1969_);
lean_del_object(v___x_1966_);
lean_dec_ref(v_val_1964_);
lean_dec(v___x_1955_);
lean_dec(v_indName_1943_);
v_a_2018_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_1974_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_1974_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
lean_dec(v_a_1963_);
lean_dec(v___x_1955_);
lean_dec(v_indName_1943_);
v___x_2027_ = lean_obj_once(&l_Lean_mkCtorIdx___lam__3___closed__2, &l_Lean_mkCtorIdx___lam__3___closed__2_once, _init_l_Lean_mkCtorIdx___lam__3___closed__2);
v___x_2028_ = l_panic___at___00Lean_mkCtorIdx_spec__11(v___x_2027_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
return v___x_2028_;
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v___x_1955_);
lean_dec(v_indName_1943_);
v_a_2029_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_1962_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_1962_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
else
{
lean_object* v___x_2037_; lean_object* v___x_2039_; 
lean_dec(v___x_1955_);
lean_dec(v_indName_1943_);
v___x_2037_ = lean_box(0);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_2037_);
v___x_2039_ = v___x_1959_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2037_);
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
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3___boxed(lean_object* v_indName_2042_, lean_object* v___x_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
uint8_t v___x_22151__boxed_2049_; lean_object* v_res_2050_; 
v___x_22151__boxed_2049_ = lean_unbox(v___x_2043_);
v_res_2050_ = l_Lean_mkCtorIdx___lam__3(v_indName_2042_, v___x_22151__boxed_2049_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__4(lean_object* v___x_2051_, lean_object* v_e_2052_){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = l_Lean_indentD(v_e_2052_);
v___x_2054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2051_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5(lean_object* v___f_2055_, lean_object* v___f_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v___x_2062_; 
v___x_2062_ = l_Lean_Meta_mapErrorImp___redArg(v___f_2055_, v___f_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
v_a_2071_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2062_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2062_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5___boxed(lean_object* v___f_2079_, lean_object* v___f_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_mkCtorIdx___lam__5(v___f_2079_, v___f_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
return v_res_2086_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___closed__1(void){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = ((lean_object*)(l_Lean_mkCtorIdx___closed__0));
v___x_2089_ = l_Lean_stringToMessageData(v___x_2088_);
return v___x_2089_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___closed__3(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = ((lean_object*)(l_Lean_mkCtorIdx___closed__2));
v___x_2092_ = l_Lean_stringToMessageData(v___x_2091_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx(lean_object* v_indName_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v___x_2099_; uint8_t v___x_2100_; lean_object* v___x_2101_; lean_object* v___f_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___f_2107_; lean_object* v___f_2108_; uint8_t v___x_2109_; 
v___x_2099_ = lean_obj_once(&l_Lean_mkCtorIdx___closed__1, &l_Lean_mkCtorIdx___closed__1_once, _init_l_Lean_mkCtorIdx___closed__1);
v___x_2100_ = 0;
v___x_2101_ = lean_box(v___x_2100_);
lean_inc_n(v_indName_2093_, 2);
v___f_2102_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__3___boxed), 7, 2);
lean_closure_set(v___f_2102_, 0, v_indName_2093_);
lean_closure_set(v___f_2102_, 1, v___x_2101_);
v___x_2103_ = l_Lean_MessageData_ofConstName(v_indName_2093_, v___x_2100_);
v___x_2104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2099_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = lean_obj_once(&l_Lean_mkCtorIdx___closed__3, &l_Lean_mkCtorIdx___closed__3_once, _init_l_Lean_mkCtorIdx___closed__3);
v___x_2106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2104_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
v___f_2107_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__4), 2, 1);
lean_closure_set(v___f_2107_, 0, v___x_2106_);
v___f_2108_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__5___boxed), 7, 2);
lean_closure_set(v___f_2108_, 0, v___f_2102_);
lean_closure_set(v___f_2108_, 1, v___f_2107_);
v___x_2109_ = l_Lean_isPrivateName(v_indName_2093_);
lean_dec(v_indName_2093_);
if (v___x_2109_ == 0)
{
uint8_t v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = 1;
v___x_2111_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(v___f_2108_, v___x_2110_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
return v___x_2111_;
}
else
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__12___redArg(v___f_2108_, v___x_2100_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
return v___x_2112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___boxed(lean_object* v_indName_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Lean_mkCtorIdx(v_indName_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(uint8_t v___x_2120_, lean_object* v___x_2121_, lean_object* v_as_2122_, lean_object* v_as_x27_2123_, lean_object* v_b_2124_, lean_object* v_a_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_2120_, v___x_2121_, v_as_x27_2123_, v_b_2124_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___boxed(lean_object* v___x_2132_, lean_object* v___x_2133_, lean_object* v_as_2134_, lean_object* v_as_x27_2135_, lean_object* v_b_2136_, lean_object* v_a_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
uint8_t v___x_22460__boxed_2143_; lean_object* v_res_2144_; 
v___x_22460__boxed_2143_ = lean_unbox(v___x_2132_);
v_res_2144_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(v___x_22460__boxed_2143_, v___x_2133_, v_as_2134_, v_as_x27_2135_, v_b_2136_, v_a_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v_as_x27_2135_);
lean_dec(v_as_2134_);
lean_dec_ref(v___x_2133_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10(lean_object* v_00_u03b1_2145_, lean_object* v_name_2146_, uint8_t v_bi_2147_, lean_object* v_type_2148_, lean_object* v_k_2149_, uint8_t v_kind_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_2146_, v_bi_2147_, v_type_2148_, v_k_2149_, v_kind_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2157_, lean_object* v_name_2158_, lean_object* v_bi_2159_, lean_object* v_type_2160_, lean_object* v_k_2161_, lean_object* v_kind_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
uint8_t v_bi_boxed_2168_; uint8_t v_kind_boxed_2169_; lean_object* v_res_2170_; 
v_bi_boxed_2168_ = lean_unbox(v_bi_2159_);
v_kind_boxed_2169_ = lean_unbox(v_kind_2162_);
v_res_2170_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10(v_00_u03b1_2157_, v_name_2158_, v_bi_boxed_2168_, v_type_2160_, v_k_2161_, v_kind_boxed_2169_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7(lean_object* v_00_u03b1_2171_, lean_object* v_name_2172_, lean_object* v_type_2173_, lean_object* v_k_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v_name_2172_, v_type_2173_, v_k_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___boxed(lean_object* v_00_u03b1_2181_, lean_object* v_name_2182_, lean_object* v_type_2183_, lean_object* v_k_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7(v_00_u03b1_2181_, v_name_2182_, v_type_2183_, v_k_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13(lean_object* v_env_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___redArg(v_env_2191_, v___y_2193_, v___y_2195_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13___boxed(lean_object* v_env_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_mkCtorIdx_spec__9_spec__13(v_env_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16(lean_object* v_00_u03b1_2205_, lean_object* v_bs_2206_, lean_object* v_k_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___redArg(v_bs_2206_, v_k_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16___boxed(lean_object* v_00_u03b1_2214_, lean_object* v_bs_2215_, lean_object* v_k_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10_spec__16(v_00_u03b1_2214_, v_bs_2215_, v_k_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec_ref(v_bs_2215_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10(lean_object* v_00_u03b1_2223_, lean_object* v_bs_2224_, lean_object* v_k_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v___x_2231_; 
v___x_2231_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___redArg(v_bs_2224_, v_k_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10___boxed(lean_object* v_00_u03b1_2232_, lean_object* v_bs_2233_, lean_object* v_k_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__10(v_00_u03b1_2232_, v_bs_2233_, v_k_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(lean_object* v_00_u03b1_2241_, lean_object* v_constName_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2249_, lean_object* v_constName_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(v_00_u03b1_2249_, v_constName_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(lean_object* v_00_u03b1_2257_, lean_object* v_msg_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2265_, lean_object* v_msg_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(v_00_u03b1_2265_, v_msg_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7(lean_object* v_00_u03b1_2273_, lean_object* v_ref_2274_, lean_object* v_constName_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_2274_, v_constName_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___boxed(lean_object* v_00_u03b1_2282_, lean_object* v_ref_2283_, lean_object* v_constName_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7(v_00_u03b1_2282_, v_ref_2283_, v_constName_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v_ref_2283_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18(lean_object* v_00_u03b1_2291_, lean_object* v_ref_2292_, lean_object* v_msg_2293_, lean_object* v_declHint_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___redArg(v_ref_2292_, v_msg_2293_, v_declHint_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18___boxed(lean_object* v_00_u03b1_2301_, lean_object* v_ref_2302_, lean_object* v_msg_2303_, lean_object* v_declHint_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18(v_00_u03b1_2301_, v_ref_2302_, v_msg_2303_, v_declHint_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v_ref_2302_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23(lean_object* v_msg_2311_, lean_object* v_declHint_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___redArg(v_msg_2311_, v_declHint_2312_, v___y_2316_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23___boxed(lean_object* v_msg_2319_, lean_object* v_declHint_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__22_spec__23(v_msg_2319_, v_declHint_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23(lean_object* v_00_u03b1_2327_, lean_object* v_ref_2328_, lean_object* v_msg_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v___x_2335_; 
v___x_2335_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___redArg(v_ref_2328_, v_msg_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23___boxed(lean_object* v_00_u03b1_2336_, lean_object* v_ref_2337_, lean_object* v_msg_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__18_spec__23(v_00_u03b1_2336_, v_ref_2337_, v_msg_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v_ref_2337_);
return v_res_2344_;
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
