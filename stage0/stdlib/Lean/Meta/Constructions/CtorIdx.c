// Lean compiler output
// Module: Lean.Meta.Constructions.CtorIdx
// Imports: public import Lean.Meta.Basic import Lean.AddDecl import Lean.Meta.CompletionName import Lean.Linter.Deprecated
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_compileDecls(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object*, lean_object*);
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_deprecatedAttr;
lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Lean_getMaxHeight(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "genCtorIdx"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(121, 142, 77, 16, 50, 110, 46, 202)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "generate the `CtorIdx` functions for inductive datatypes"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Constructions"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(224, 107, 212, 234, 74, 49, 105, 87)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CtorIdx"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(149, 119, 104, 54, 230, 159, 208, 234)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 246, 214, 203, 234, 6, 143, 204)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(134, 216, 207, 23, 24, 47, 82, 122)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx;
static const lean_string_object l_mkToCtorIdxName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "toCtorIdx"};
static const lean_object* l_mkToCtorIdxName___closed__0 = (const lean_object*)&l_mkToCtorIdxName___closed__0_value;
LEAN_EXPORT lean_object* l_mkToCtorIdxName(lean_object*);
static const lean_string_object l_mkCtorIdxName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ctorIdx"};
static const lean_object* l_mkCtorIdxName___closed__0 = (const lean_object*)&l_mkCtorIdxName___closed__0_value;
LEAN_EXPORT lean_object* l_mkCtorIdxName(lean_object*);
LEAN_EXPORT lean_object* l_isCtorIdxCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_isCtorIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_isCtorIdx_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_isCtorIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_isCtorIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00mkCtorIdx_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00mkCtorIdx_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00mkCtorIdx_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00mkCtorIdx_spec__13___closed__0 = (const lean_object*)&l_panic___at___00mkCtorIdx_spec__13___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00mkCtorIdx_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00mkCtorIdx_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_mkCtorIdx___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkCtorIdx___lam__0___closed__0;
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__0(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__0___boxed(lean_object**);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00mkCtorIdx_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00mkCtorIdx_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00mkCtorIdx_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_mkCtorIdx___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "2025-08-25"};
static const lean_object* l_mkCtorIdx___lam__1___closed__0 = (const lean_object*)&l_mkCtorIdx___lam__1___closed__0_value;
static const lean_ctor_object l_mkCtorIdx___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_mkCtorIdx___lam__1___closed__0_value)}};
static const lean_object* l_mkCtorIdx___lam__1___closed__1 = (const lean_object*)&l_mkCtorIdx___lam__1___closed__1_value;
static const lean_string_object l_mkCtorIdx___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_mkCtorIdx___lam__1___closed__2 = (const lean_object*)&l_mkCtorIdx___lam__1___closed__2_value;
static const lean_ctor_object l_mkCtorIdx___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_mkCtorIdx___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_mkCtorIdx___lam__1___closed__3 = (const lean_object*)&l_mkCtorIdx___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_mkCtorIdx___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_mkCtorIdx___lam__2___closed__0 = (const lean_object*)&l_mkCtorIdx___lam__2___closed__0_value;
static const lean_ctor_object l_mkCtorIdx___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_mkCtorIdx___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_mkCtorIdx___lam__2___closed__1 = (const lean_object*)&l_mkCtorIdx___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00mkCtorIdx_spec__3(lean_object*, lean_object*);
static const lean_string_object l_mkCtorIdx___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Constructions.CtorIdx"};
static const lean_object* l_mkCtorIdx___lam__3___closed__0 = (const lean_object*)&l_mkCtorIdx___lam__3___closed__0_value;
static const lean_string_object l_mkCtorIdx___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mkCtorIdx"};
static const lean_object* l_mkCtorIdx___lam__3___closed__1 = (const lean_object*)&l_mkCtorIdx___lam__3___closed__1_value;
static lean_once_cell_t l_mkCtorIdx___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkCtorIdx___lam__3___closed__2;
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_mkCtorIdx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "failed to construct `T.ctorIdx` for `"};
static const lean_object* l_mkCtorIdx___closed__0 = (const lean_object*)&l_mkCtorIdx___closed__0_value;
static lean_once_cell_t l_mkCtorIdx___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkCtorIdx___closed__1;
static const lean_string_object l_mkCtorIdx___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`:"};
static const lean_object* l_mkCtorIdx___closed__2 = (const lean_object*)&l_mkCtorIdx___closed__2_value;
static lean_once_cell_t l_mkCtorIdx___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkCtorIdx___closed__3;
LEAN_EXPORT lean_object* l_mkCtorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_71_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_72_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_73_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v___x_70_, v___x_71_, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4____boxed(lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l___private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_mkToCtorIdxName(lean_object* v_indName_77_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = ((lean_object*)(l_mkToCtorIdxName___closed__0));
v___x_79_ = l_Lean_Name_str___override(v_indName_77_, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdxName(lean_object* v_indName_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = ((lean_object*)(l_mkCtorIdxName___closed__0));
v___x_83_ = l_Lean_Name_str___override(v_indName_81_, v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_isCtorIdxCore_x3f(lean_object* v_env_84_, lean_object* v_declName_85_){
_start:
{
if (lean_obj_tag(v_declName_85_) == 1)
{
lean_object* v_pre_86_; lean_object* v_str_87_; lean_object* v___x_88_; uint8_t v___x_89_; 
v_pre_86_ = lean_ctor_get(v_declName_85_, 0);
lean_inc(v_pre_86_);
v_str_87_ = lean_ctor_get(v_declName_85_, 1);
lean_inc_ref(v_str_87_);
lean_dec_ref(v_declName_85_);
v___x_88_ = ((lean_object*)(l_mkCtorIdxName___closed__0));
v___x_89_ = lean_string_dec_eq(v_str_87_, v___x_88_);
lean_dec_ref(v_str_87_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
lean_dec(v_pre_86_);
lean_dec_ref(v_env_84_);
v___x_90_ = lean_box(0);
return v___x_90_;
}
else
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_isInductiveCore_x3f(v_env_84_, v_pre_86_);
return v___x_91_;
}
}
else
{
lean_object* v___x_92_; 
lean_dec(v_declName_85_);
lean_dec_ref(v_env_84_);
v___x_92_ = lean_box(0);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_isCtorIdx_x3f___redArg(lean_object* v_declName_93_, lean_object* v_a_94_){
_start:
{
lean_object* v___x_96_; lean_object* v_env_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_96_ = lean_st_ref_get(v_a_94_);
v_env_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc_ref(v_env_97_);
lean_dec(v___x_96_);
v___x_98_ = l_isCtorIdxCore_x3f(v_env_97_, v_declName_93_);
v___x_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_isCtorIdx_x3f___redArg___boxed(lean_object* v_declName_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_isCtorIdx_x3f___redArg(v_declName_100_, v_a_101_);
lean_dec(v_a_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_isCtorIdx_x3f(lean_object* v_declName_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_isCtorIdx_x3f___redArg(v_declName_104_, v_a_108_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_isCtorIdx_x3f___boxed(lean_object* v_declName_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_isCtorIdx_x3f(v_declName_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
return v_res_117_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00mkCtorIdx_spec__0(lean_object* v_opts_118_, lean_object* v_opt_119_){
_start:
{
lean_object* v_name_120_; lean_object* v_defValue_121_; lean_object* v_map_122_; lean_object* v___x_123_; 
v_name_120_ = lean_ctor_get(v_opt_119_, 0);
v_defValue_121_ = lean_ctor_get(v_opt_119_, 1);
v_map_122_ = lean_ctor_get(v_opts_118_, 0);
v___x_123_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_122_, v_name_120_);
if (lean_obj_tag(v___x_123_) == 0)
{
uint8_t v___x_124_; 
v___x_124_ = lean_unbox(v_defValue_121_);
return v___x_124_;
}
else
{
lean_object* v_val_125_; 
v_val_125_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_val_125_);
lean_dec_ref(v___x_123_);
if (lean_obj_tag(v_val_125_) == 1)
{
uint8_t v_v_126_; 
v_v_126_ = lean_ctor_get_uint8(v_val_125_, 0);
lean_dec_ref(v_val_125_);
return v_v_126_;
}
else
{
uint8_t v___x_127_; 
lean_dec(v_val_125_);
v___x_127_ = lean_unbox(v_defValue_121_);
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00mkCtorIdx_spec__0___boxed(lean_object* v_opts_128_, lean_object* v_opt_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_Lean_Option_get___at___00mkCtorIdx_spec__0(v_opts_128_, v_opt_129_);
lean_dec_ref(v_opt_129_);
lean_dec_ref(v_opts_128_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(lean_object* v_constName_132_, uint8_t v_skipRealize_133_, lean_object* v___y_134_){
_start:
{
lean_object* v___x_136_; lean_object* v_env_137_; uint8_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_136_ = lean_st_ref_get(v___y_134_);
v_env_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc_ref(v_env_137_);
lean_dec(v___x_136_);
v___x_138_ = l_Lean_Environment_contains(v_env_137_, v_constName_132_, v_skipRealize_133_);
v___x_139_ = lean_box(v___x_138_);
v___x_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg___boxed(lean_object* v_constName_141_, lean_object* v_skipRealize_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
uint8_t v_skipRealize_boxed_145_; lean_object* v_res_146_; 
v_skipRealize_boxed_145_ = lean_unbox(v_skipRealize_142_);
v_res_146_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(v_constName_141_, v_skipRealize_boxed_145_, v___y_143_);
lean_dec(v___y_143_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1(lean_object* v_constName_147_, uint8_t v_skipRealize_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(v_constName_147_, v_skipRealize_148_, v___y_152_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1___boxed(lean_object* v_constName_155_, lean_object* v_skipRealize_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
uint8_t v_skipRealize_boxed_162_; lean_object* v_res_163_; 
v_skipRealize_boxed_162_ = lean_unbox(v_skipRealize_156_);
v_res_163_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1(v_constName_155_, v_skipRealize_boxed_162_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0(lean_object* v_k_164_, lean_object* v_b_165_, lean_object* v_c_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0___boxed(lean_object* v_k_173_, lean_object* v_b_174_, lean_object* v_c_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0(v_k_173_, v_b_174_, v_c_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(lean_object* v_type_182_, lean_object* v_maxFVars_x3f_183_, lean_object* v_k_184_, uint8_t v_cleanupAnnotations_185_, uint8_t v_whnfType_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___f_192_; lean_object* v___x_193_; 
v___f_192_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_192_, 0, v_k_184_);
v___x_193_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_182_, v_maxFVars_x3f_183_, v___f_192_, v_cleanupAnnotations_185_, v_whnfType_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_193_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
v_a_202_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_193_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_193_);
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
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___boxed(lean_object* v_type_210_, lean_object* v_maxFVars_x3f_211_, lean_object* v_k_212_, lean_object* v_cleanupAnnotations_213_, lean_object* v_whnfType_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_220_; uint8_t v_whnfType_boxed_221_; lean_object* v_res_222_; 
v_cleanupAnnotations_boxed_220_ = lean_unbox(v_cleanupAnnotations_213_);
v_whnfType_boxed_221_ = lean_unbox(v_whnfType_214_);
v_res_222_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(v_type_210_, v_maxFVars_x3f_211_, v_k_212_, v_cleanupAnnotations_boxed_220_, v_whnfType_boxed_221_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5(lean_object* v_00_u03b1_223_, lean_object* v_type_224_, lean_object* v_maxFVars_x3f_225_, lean_object* v_k_226_, uint8_t v_cleanupAnnotations_227_, uint8_t v_whnfType_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(v_type_224_, v_maxFVars_x3f_225_, v_k_226_, v_cleanupAnnotations_227_, v_whnfType_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___boxed(lean_object* v_00_u03b1_235_, lean_object* v_type_236_, lean_object* v_maxFVars_x3f_237_, lean_object* v_k_238_, lean_object* v_cleanupAnnotations_239_, lean_object* v_whnfType_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_246_; uint8_t v_whnfType_boxed_247_; lean_object* v_res_248_; 
v_cleanupAnnotations_boxed_246_ = lean_unbox(v_cleanupAnnotations_239_);
v_whnfType_boxed_247_ = lean_unbox(v_whnfType_240_);
v_res_248_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5(v_00_u03b1_235_, v_type_236_, v_maxFVars_x3f_237_, v_k_238_, v_cleanupAnnotations_boxed_246_, v_whnfType_boxed_247_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(lean_object* v_name_249_, lean_object* v_levelParams_250_, lean_object* v_type_251_, lean_object* v_value_252_, lean_object* v_hints_253_, lean_object* v___y_254_){
_start:
{
lean_object* v___x_256_; uint8_t v___y_258_; uint8_t v___y_265_; lean_object* v_env_268_; uint8_t v___x_269_; 
v___x_256_ = lean_st_ref_get(v___y_254_);
v_env_268_ = lean_ctor_get(v___x_256_, 0);
lean_inc_ref_n(v_env_268_, 2);
lean_dec(v___x_256_);
v___x_269_ = l_Lean_Environment_hasUnsafe(v_env_268_, v_type_251_);
if (v___x_269_ == 0)
{
uint8_t v___x_270_; 
v___x_270_ = l_Lean_Environment_hasUnsafe(v_env_268_, v_value_252_);
v___y_265_ = v___x_270_;
goto v___jp_264_;
}
else
{
lean_dec_ref(v_env_268_);
v___y_265_ = v___x_269_;
goto v___jp_264_;
}
v___jp_257_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
lean_inc(v_name_249_);
v___x_259_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_259_, 0, v_name_249_);
lean_ctor_set(v___x_259_, 1, v_levelParams_250_);
lean_ctor_set(v___x_259_, 2, v_type_251_);
v___x_260_ = lean_box(0);
v___x_261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_261_, 0, v_name_249_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_262_, 0, v___x_259_);
lean_ctor_set(v___x_262_, 1, v_value_252_);
lean_ctor_set(v___x_262_, 2, v_hints_253_);
lean_ctor_set(v___x_262_, 3, v___x_261_);
lean_ctor_set_uint8(v___x_262_, sizeof(void*)*4, v___y_258_);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
v___jp_264_:
{
if (v___y_265_ == 0)
{
uint8_t v___x_266_; 
v___x_266_ = 1;
v___y_258_ = v___x_266_;
goto v___jp_257_;
}
else
{
uint8_t v___x_267_; 
v___x_267_ = 0;
v___y_258_ = v___x_267_;
goto v___jp_257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg___boxed(lean_object* v_name_271_, lean_object* v_levelParams_272_, lean_object* v_type_273_, lean_object* v_value_274_, lean_object* v_hints_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(v_name_271_, v_levelParams_272_, v_type_273_, v_value_274_, v_hints_275_, v___y_276_);
lean_dec(v___y_276_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8(lean_object* v_name_279_, lean_object* v_levelParams_280_, lean_object* v_type_281_, lean_object* v_value_282_, lean_object* v_hints_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(v_name_279_, v_levelParams_280_, v_type_281_, v_value_282_, v_hints_283_, v___y_287_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___boxed(lean_object* v_name_290_, lean_object* v_levelParams_291_, lean_object* v_type_292_, lean_object* v_value_293_, lean_object* v_hints_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8(v_name_290_, v_levelParams_291_, v_type_292_, v_value_293_, v_hints_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00mkCtorIdx_spec__13(lean_object* v_msg_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v___f_308_; lean_object* v___x_26644__overap_309_; lean_object* v___x_310_; 
v___f_308_ = ((lean_object*)(l_panic___at___00mkCtorIdx_spec__13___closed__0));
v___x_26644__overap_309_ = lean_panic_fn_borrowed(v___f_308_, v_msg_302_);
lean_inc(v___y_306_);
lean_inc_ref(v___y_305_);
lean_inc(v___y_304_);
lean_inc_ref(v___y_303_);
v___x_310_ = lean_apply_5(v___x_26644__overap_309_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, lean_box(0));
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00mkCtorIdx_spec__13___boxed(lean_object* v_msg_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_panic___at___00mkCtorIdx_spec__13(v_msg_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(lean_object* v___y_318_, uint8_t v_isExporting_319_, lean_object* v___x_320_, lean_object* v___y_321_, lean_object* v___x_322_, lean_object* v_a_x3f_323_){
_start:
{
lean_object* v___x_325_; lean_object* v_env_326_; lean_object* v_nextMacroScope_327_; lean_object* v_ngen_328_; lean_object* v_auxDeclNGen_329_; lean_object* v_traceState_330_; lean_object* v_messages_331_; lean_object* v_infoState_332_; lean_object* v_snapshotTasks_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_358_; 
v___x_325_ = lean_st_ref_take(v___y_318_);
v_env_326_ = lean_ctor_get(v___x_325_, 0);
v_nextMacroScope_327_ = lean_ctor_get(v___x_325_, 1);
v_ngen_328_ = lean_ctor_get(v___x_325_, 2);
v_auxDeclNGen_329_ = lean_ctor_get(v___x_325_, 3);
v_traceState_330_ = lean_ctor_get(v___x_325_, 4);
v_messages_331_ = lean_ctor_get(v___x_325_, 6);
v_infoState_332_ = lean_ctor_get(v___x_325_, 7);
v_snapshotTasks_333_ = lean_ctor_get(v___x_325_, 8);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; 
v_unused_359_ = lean_ctor_get(v___x_325_, 5);
lean_dec(v_unused_359_);
v___x_335_ = v___x_325_;
v_isShared_336_ = v_isSharedCheck_358_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_snapshotTasks_333_);
lean_inc(v_infoState_332_);
lean_inc(v_messages_331_);
lean_inc(v_traceState_330_);
lean_inc(v_auxDeclNGen_329_);
lean_inc(v_ngen_328_);
lean_inc(v_nextMacroScope_327_);
lean_inc(v_env_326_);
lean_dec(v___x_325_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_358_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_337_ = l_Lean_Environment_setExporting(v_env_326_, v_isExporting_319_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 5, v___x_320_);
lean_ctor_set(v___x_335_, 0, v___x_337_);
v___x_339_ = v___x_335_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_nextMacroScope_327_);
lean_ctor_set(v_reuseFailAlloc_357_, 2, v_ngen_328_);
lean_ctor_set(v_reuseFailAlloc_357_, 3, v_auxDeclNGen_329_);
lean_ctor_set(v_reuseFailAlloc_357_, 4, v_traceState_330_);
lean_ctor_set(v_reuseFailAlloc_357_, 5, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_357_, 6, v_messages_331_);
lean_ctor_set(v_reuseFailAlloc_357_, 7, v_infoState_332_);
lean_ctor_set(v_reuseFailAlloc_357_, 8, v_snapshotTasks_333_);
v___x_339_ = v_reuseFailAlloc_357_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v_mctx_342_; lean_object* v_zetaDeltaFVarIds_343_; lean_object* v_postponed_344_; lean_object* v_diag_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_355_; 
v___x_340_ = lean_st_ref_set(v___y_318_, v___x_339_);
v___x_341_ = lean_st_ref_take(v___y_321_);
v_mctx_342_ = lean_ctor_get(v___x_341_, 0);
v_zetaDeltaFVarIds_343_ = lean_ctor_get(v___x_341_, 2);
v_postponed_344_ = lean_ctor_get(v___x_341_, 3);
v_diag_345_ = lean_ctor_get(v___x_341_, 4);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_355_ == 0)
{
lean_object* v_unused_356_; 
v_unused_356_ = lean_ctor_get(v___x_341_, 1);
lean_dec(v_unused_356_);
v___x_347_ = v___x_341_;
v_isShared_348_ = v_isSharedCheck_355_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_diag_345_);
lean_inc(v_postponed_344_);
lean_inc(v_zetaDeltaFVarIds_343_);
lean_inc(v_mctx_342_);
lean_dec(v___x_341_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_355_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 1, v___x_322_);
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_mctx_342_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_354_, 2, v_zetaDeltaFVarIds_343_);
lean_ctor_set(v_reuseFailAlloc_354_, 3, v_postponed_344_);
lean_ctor_set(v_reuseFailAlloc_354_, 4, v_diag_345_);
v___x_350_ = v_reuseFailAlloc_354_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_351_ = lean_st_ref_set(v___y_321_, v___x_350_);
v___x_352_ = lean_box(0);
v___x_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
return v___x_353_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0___boxed(lean_object* v___y_360_, lean_object* v_isExporting_361_, lean_object* v___x_362_, lean_object* v___y_363_, lean_object* v___x_364_, lean_object* v_a_x3f_365_, lean_object* v___y_366_){
_start:
{
uint8_t v_isExporting_boxed_367_; lean_object* v_res_368_; 
v_isExporting_boxed_367_ = lean_unbox(v_isExporting_361_);
v_res_368_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(v___y_360_, v_isExporting_boxed_367_, v___x_362_, v___y_363_, v___x_364_, v_a_x3f_365_);
lean_dec(v_a_x3f_365_);
lean_dec(v___y_363_);
lean_dec(v___y_360_);
return v_res_368_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_369_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0);
v___x_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1);
v___x_375_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
lean_ctor_set(v___x_375_, 2, v___x_374_);
lean_ctor_set(v___x_375_, 3, v___x_374_);
lean_ctor_set(v___x_375_, 4, v___x_374_);
lean_ctor_set(v___x_375_, 5, v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(lean_object* v_x_376_, uint8_t v_isExporting_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v___x_383_; lean_object* v_env_384_; uint8_t v_isExporting_385_; lean_object* v___x_386_; lean_object* v_env_387_; lean_object* v_nextMacroScope_388_; lean_object* v_ngen_389_; lean_object* v_auxDeclNGen_390_; lean_object* v_traceState_391_; lean_object* v_messages_392_; lean_object* v_infoState_393_; lean_object* v_snapshotTasks_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_448_; 
v___x_383_ = lean_st_ref_get(v___y_381_);
v_env_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc_ref(v_env_384_);
lean_dec(v___x_383_);
v_isExporting_385_ = lean_ctor_get_uint8(v_env_384_, sizeof(void*)*8);
lean_dec_ref(v_env_384_);
v___x_386_ = lean_st_ref_take(v___y_381_);
v_env_387_ = lean_ctor_get(v___x_386_, 0);
v_nextMacroScope_388_ = lean_ctor_get(v___x_386_, 1);
v_ngen_389_ = lean_ctor_get(v___x_386_, 2);
v_auxDeclNGen_390_ = lean_ctor_get(v___x_386_, 3);
v_traceState_391_ = lean_ctor_get(v___x_386_, 4);
v_messages_392_ = lean_ctor_get(v___x_386_, 6);
v_infoState_393_ = lean_ctor_get(v___x_386_, 7);
v_snapshotTasks_394_ = lean_ctor_get(v___x_386_, 8);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; 
v_unused_449_ = lean_ctor_get(v___x_386_, 5);
lean_dec(v_unused_449_);
v___x_396_ = v___x_386_;
v_isShared_397_ = v_isSharedCheck_448_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_snapshotTasks_394_);
lean_inc(v_infoState_393_);
lean_inc(v_messages_392_);
lean_inc(v_traceState_391_);
lean_inc(v_auxDeclNGen_390_);
lean_inc(v_ngen_389_);
lean_inc(v_nextMacroScope_388_);
lean_inc(v_env_387_);
lean_dec(v___x_386_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_448_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_398_ = l_Lean_Environment_setExporting(v_env_387_, v_isExporting_377_);
v___x_399_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 5, v___x_399_);
lean_ctor_set(v___x_396_, 0, v___x_398_);
v___x_401_ = v___x_396_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_nextMacroScope_388_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_ngen_389_);
lean_ctor_set(v_reuseFailAlloc_447_, 3, v_auxDeclNGen_390_);
lean_ctor_set(v_reuseFailAlloc_447_, 4, v_traceState_391_);
lean_ctor_set(v_reuseFailAlloc_447_, 5, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_447_, 6, v_messages_392_);
lean_ctor_set(v_reuseFailAlloc_447_, 7, v_infoState_393_);
lean_ctor_set(v_reuseFailAlloc_447_, 8, v_snapshotTasks_394_);
v___x_401_ = v_reuseFailAlloc_447_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v_mctx_404_; lean_object* v_zetaDeltaFVarIds_405_; lean_object* v_postponed_406_; lean_object* v_diag_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_445_; 
v___x_402_ = lean_st_ref_set(v___y_381_, v___x_401_);
v___x_403_ = lean_st_ref_take(v___y_379_);
v_mctx_404_ = lean_ctor_get(v___x_403_, 0);
v_zetaDeltaFVarIds_405_ = lean_ctor_get(v___x_403_, 2);
v_postponed_406_ = lean_ctor_get(v___x_403_, 3);
v_diag_407_ = lean_ctor_get(v___x_403_, 4);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; 
v_unused_446_ = lean_ctor_get(v___x_403_, 1);
lean_dec(v_unused_446_);
v___x_409_ = v___x_403_;
v_isShared_410_ = v_isSharedCheck_445_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_diag_407_);
lean_inc(v_postponed_406_);
lean_inc(v_zetaDeltaFVarIds_405_);
lean_inc(v_mctx_404_);
lean_dec(v___x_403_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_445_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_411_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 1, v___x_411_);
v___x_413_ = v___x_409_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_mctx_404_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v___x_411_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_zetaDeltaFVarIds_405_);
lean_ctor_set(v_reuseFailAlloc_444_, 3, v_postponed_406_);
lean_ctor_set(v_reuseFailAlloc_444_, 4, v_diag_407_);
v___x_413_ = v_reuseFailAlloc_444_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; lean_object* v_r_415_; 
v___x_414_ = lean_st_ref_set(v___y_379_, v___x_413_);
lean_inc(v___y_381_);
lean_inc_ref(v___y_380_);
lean_inc(v___y_379_);
lean_inc_ref(v___y_378_);
v_r_415_ = lean_apply_5(v_x_376_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, lean_box(0));
if (lean_obj_tag(v_r_415_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_432_; 
v_a_416_ = lean_ctor_get(v_r_415_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v_r_415_);
if (v_isSharedCheck_432_ == 0)
{
v___x_418_ = v_r_415_;
v_isShared_419_ = v_isSharedCheck_432_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v_r_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_432_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
lean_inc(v_a_416_);
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 1);
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_431_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
v___x_422_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(v___y_381_, v_isExporting_385_, v___x_399_, v___y_379_, v___x_411_, v___x_421_);
lean_dec_ref(v___x_421_);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_429_ == 0)
{
lean_object* v_unused_430_; 
v_unused_430_ = lean_ctor_get(v___x_422_, 0);
lean_dec(v_unused_430_);
v___x_424_ = v___x_422_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_dec(v___x_422_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v_a_416_);
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_416_);
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
else
{
lean_object* v_a_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
v_a_433_ = lean_ctor_get(v_r_415_, 0);
lean_inc(v_a_433_);
lean_dec_ref(v_r_415_);
v___x_434_ = lean_box(0);
v___x_435_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(v___y_381_, v_isExporting_385_, v___x_399_, v___y_379_, v___x_411_, v___x_434_);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_442_ == 0)
{
lean_object* v_unused_443_; 
v_unused_443_ = lean_ctor_get(v___x_435_, 0);
lean_dec(v_unused_443_);
v___x_437_ = v___x_435_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_dec(v___x_435_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
lean_ctor_set_tag(v___x_437_, 1);
lean_ctor_set(v___x_437_, 0, v_a_433_);
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_433_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___boxed(lean_object* v_x_450_, lean_object* v_isExporting_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
uint8_t v_isExporting_boxed_457_; lean_object* v_res_458_; 
v_isExporting_boxed_457_ = lean_unbox(v_isExporting_451_);
v_res_458_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(v_x_450_, v_isExporting_boxed_457_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14(lean_object* v_00_u03b1_459_, lean_object* v_x_460_, uint8_t v_isExporting_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(v_x_460_, v_isExporting_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___boxed(lean_object* v_00_u03b1_468_, lean_object* v_x_469_, lean_object* v_isExporting_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
uint8_t v_isExporting_boxed_476_; lean_object* v_res_477_; 
v_isExporting_boxed_476_ = lean_unbox(v_isExporting_470_);
v_res_477_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14(v_00_u03b1_468_, v_x_469_, v_isExporting_boxed_476_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11(lean_object* v_msgData_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v___x_484_; lean_object* v_env_485_; lean_object* v___x_486_; lean_object* v_mctx_487_; lean_object* v_lctx_488_; lean_object* v_options_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_484_ = lean_st_ref_get(v___y_482_);
v_env_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc_ref(v_env_485_);
lean_dec(v___x_484_);
v___x_486_ = lean_st_ref_get(v___y_480_);
v_mctx_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc_ref(v_mctx_487_);
lean_dec(v___x_486_);
v_lctx_488_ = lean_ctor_get(v___y_479_, 2);
v_options_489_ = lean_ctor_get(v___y_481_, 2);
lean_inc_ref(v_options_489_);
lean_inc_ref(v_lctx_488_);
v___x_490_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_490_, 0, v_env_485_);
lean_ctor_set(v___x_490_, 1, v_mctx_487_);
lean_ctor_set(v___x_490_, 2, v_lctx_488_);
lean_ctor_set(v___x_490_, 3, v_options_489_);
v___x_491_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
lean_ctor_set(v___x_491_, 1, v_msgData_478_);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11___boxed(lean_object* v_msgData_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11(v_msgData_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(lean_object* v_msg_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_ref_506_; lean_object* v___x_507_; lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_516_; 
v_ref_506_ = lean_ctor_get(v___y_503_, 5);
v___x_507_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11(v_msg_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
v_a_508_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_516_ == 0)
{
v___x_510_ = v___x_507_;
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_507_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_514_; 
lean_inc(v_ref_506_);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v_ref_506_);
lean_ctor_set(v___x_512_, 1, v_a_508_);
if (v_isShared_511_ == 0)
{
lean_ctor_set_tag(v___x_510_, 1);
lean_ctor_set(v___x_510_, 0, v___x_512_);
v___x_514_ = v___x_510_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg___boxed(lean_object* v_msg_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v_msg_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
return v_res_523_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0(void){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_instMonadEIO(lean_box(0));
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(lean_object* v_msg_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v_toApplicative_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_598_; 
v___x_535_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0);
v___x_536_ = l_StateRefT_x27_instMonad___redArg(v___x_535_);
v_toApplicative_537_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v___x_536_, 1);
lean_dec(v_unused_599_);
v___x_539_ = v___x_536_;
v_isShared_540_ = v_isSharedCheck_598_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_toApplicative_537_);
lean_dec(v___x_536_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_598_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v_toFunctor_541_; lean_object* v_toSeq_542_; lean_object* v_toSeqLeft_543_; lean_object* v_toSeqRight_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_596_; 
v_toFunctor_541_ = lean_ctor_get(v_toApplicative_537_, 0);
v_toSeq_542_ = lean_ctor_get(v_toApplicative_537_, 2);
v_toSeqLeft_543_ = lean_ctor_get(v_toApplicative_537_, 3);
v_toSeqRight_544_ = lean_ctor_get(v_toApplicative_537_, 4);
v_isSharedCheck_596_ = !lean_is_exclusive(v_toApplicative_537_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; 
v_unused_597_ = lean_ctor_get(v_toApplicative_537_, 1);
lean_dec(v_unused_597_);
v___x_546_ = v_toApplicative_537_;
v_isShared_547_ = v_isSharedCheck_596_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_toSeqRight_544_);
lean_inc(v_toSeqLeft_543_);
lean_inc(v_toSeq_542_);
lean_inc(v_toFunctor_541_);
lean_dec(v_toApplicative_537_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_596_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___f_548_; lean_object* v___f_549_; lean_object* v___f_550_; lean_object* v___f_551_; lean_object* v___x_552_; lean_object* v___f_553_; lean_object* v___f_554_; lean_object* v___f_555_; lean_object* v___x_557_; 
v___f_548_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__1));
v___f_549_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__2));
lean_inc_ref(v_toFunctor_541_);
v___f_550_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_550_, 0, v_toFunctor_541_);
v___f_551_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_551_, 0, v_toFunctor_541_);
v___x_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_552_, 0, v___f_550_);
lean_ctor_set(v___x_552_, 1, v___f_551_);
v___f_553_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_553_, 0, v_toSeqRight_544_);
v___f_554_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_554_, 0, v_toSeqLeft_543_);
v___f_555_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_555_, 0, v_toSeq_542_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 4, v___f_553_);
lean_ctor_set(v___x_546_, 3, v___f_554_);
lean_ctor_set(v___x_546_, 2, v___f_555_);
lean_ctor_set(v___x_546_, 1, v___f_548_);
lean_ctor_set(v___x_546_, 0, v___x_552_);
v___x_557_ = v___x_546_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v___f_548_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v___f_555_);
lean_ctor_set(v_reuseFailAlloc_595_, 3, v___f_554_);
lean_ctor_set(v_reuseFailAlloc_595_, 4, v___f_553_);
v___x_557_ = v_reuseFailAlloc_595_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_559_; 
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___f_549_);
lean_ctor_set(v___x_539_, 0, v___x_557_);
v___x_559_ = v___x_539_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v___f_549_);
v___x_559_ = v_reuseFailAlloc_594_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; lean_object* v_toApplicative_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_592_; 
v___x_560_ = l_StateRefT_x27_instMonad___redArg(v___x_559_);
v_toApplicative_561_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_592_ == 0)
{
lean_object* v_unused_593_; 
v_unused_593_ = lean_ctor_get(v___x_560_, 1);
lean_dec(v_unused_593_);
v___x_563_ = v___x_560_;
v_isShared_564_ = v_isSharedCheck_592_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_toApplicative_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_592_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v_toFunctor_565_; lean_object* v_toSeq_566_; lean_object* v_toSeqLeft_567_; lean_object* v_toSeqRight_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_590_; 
v_toFunctor_565_ = lean_ctor_get(v_toApplicative_561_, 0);
v_toSeq_566_ = lean_ctor_get(v_toApplicative_561_, 2);
v_toSeqLeft_567_ = lean_ctor_get(v_toApplicative_561_, 3);
v_toSeqRight_568_ = lean_ctor_get(v_toApplicative_561_, 4);
v_isSharedCheck_590_ = !lean_is_exclusive(v_toApplicative_561_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; 
v_unused_591_ = lean_ctor_get(v_toApplicative_561_, 1);
lean_dec(v_unused_591_);
v___x_570_ = v_toApplicative_561_;
v_isShared_571_ = v_isSharedCheck_590_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_toSeqRight_568_);
lean_inc(v_toSeqLeft_567_);
lean_inc(v_toSeq_566_);
lean_inc(v_toFunctor_565_);
lean_dec(v_toApplicative_561_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_590_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___f_572_; lean_object* v___f_573_; lean_object* v___f_574_; lean_object* v___f_575_; lean_object* v___x_576_; lean_object* v___f_577_; lean_object* v___f_578_; lean_object* v___f_579_; lean_object* v___x_581_; 
v___f_572_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__3));
v___f_573_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__4));
lean_inc_ref(v_toFunctor_565_);
v___f_574_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_574_, 0, v_toFunctor_565_);
v___f_575_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_575_, 0, v_toFunctor_565_);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v___f_574_);
lean_ctor_set(v___x_576_, 1, v___f_575_);
v___f_577_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_577_, 0, v_toSeqRight_568_);
v___f_578_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_578_, 0, v_toSeqLeft_567_);
v___f_579_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_579_, 0, v_toSeq_566_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 4, v___f_577_);
lean_ctor_set(v___x_570_, 3, v___f_578_);
lean_ctor_set(v___x_570_, 2, v___f_579_);
lean_ctor_set(v___x_570_, 1, v___f_572_);
lean_ctor_set(v___x_570_, 0, v___x_576_);
v___x_581_ = v___x_570_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v___f_572_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v___f_579_);
lean_ctor_set(v_reuseFailAlloc_589_, 3, v___f_578_);
lean_ctor_set(v_reuseFailAlloc_589_, 4, v___f_577_);
v___x_581_ = v_reuseFailAlloc_589_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_583_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v___f_573_);
lean_ctor_set(v___x_563_, 0, v___x_581_);
v___x_583_ = v___x_563_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___f_573_);
v___x_583_ = v_reuseFailAlloc_588_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_30006__overap_586_; lean_object* v___x_587_; 
v___x_584_ = lean_box(0);
v___x_585_ = l_instInhabitedOfMonad___redArg(v___x_583_, v___x_584_);
v___x_30006__overap_586_ = lean_panic_fn_borrowed(v___x_585_, v_msg_529_);
lean_dec(v___x_585_);
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
v___x_587_ = lean_apply_5(v___x_30006__overap_586_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, lean_box(0));
return v___x_587_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___boxed(lean_object* v_msg_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(v_msg_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
return v_res_606_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__0));
v___x_609_ = l_Lean_stringToMessageData(v___x_608_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__2));
v___x_612_ = l_Lean_stringToMessageData(v___x_611_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_616_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6));
v___x_617_ = lean_unsigned_to_nat(11u);
v___x_618_ = lean_unsigned_to_nat(122u);
v___x_619_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__5));
v___x_620_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__4));
v___x_621_ = l_mkPanicMessageWithDecl(v___x_620_, v___x_619_, v___x_618_, v___x_617_, v___x_616_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4(lean_object* v_constName_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_636_; lean_object* v_env_637_; uint8_t v___x_638_; lean_object* v___x_639_; 
v___x_636_ = lean_st_ref_get(v___y_626_);
v_env_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc_ref(v_env_637_);
lean_dec(v___x_636_);
v___x_638_ = 0;
lean_inc(v_constName_622_);
v___x_639_ = l_Lean_Environment_findAsync_x3f(v_env_637_, v_constName_622_, v___x_638_);
if (lean_obj_tag(v___x_639_) == 1)
{
lean_object* v_val_640_; uint8_t v_kind_641_; 
v_val_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_val_640_);
lean_dec_ref(v___x_639_);
v_kind_641_ = lean_ctor_get_uint8(v_val_640_, sizeof(void*)*3);
if (v_kind_641_ == 6)
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_640_);
if (lean_obj_tag(v___x_642_) == 6)
{
lean_object* v_val_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec(v_constName_622_);
v_val_643_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_642_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_val_643_);
lean_dec(v___x_642_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
lean_ctor_set_tag(v___x_645_, 0);
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_val_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; 
lean_dec_ref(v___x_642_);
v___x_651_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7, &l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7);
v___x_652_ = l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(v___x_651_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_661_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_661_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
if (lean_obj_tag(v_a_653_) == 0)
{
lean_del_object(v___x_655_);
goto v___jp_628_;
}
else
{
lean_object* v_val_657_; lean_object* v___x_659_; 
lean_dec(v_constName_622_);
v_val_657_ = lean_ctor_get(v_a_653_, 0);
lean_inc(v_val_657_);
lean_dec_ref(v_a_653_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v_val_657_);
v___x_659_ = v___x_655_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_val_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec(v_constName_622_);
v_a_662_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_652_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_652_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
else
{
lean_dec(v_val_640_);
goto v___jp_628_;
}
}
else
{
lean_dec(v___x_639_);
goto v___jp_628_;
}
v___jp_628_:
{
lean_object* v___x_629_; uint8_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_629_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1);
v___x_630_ = 0;
v___x_631_ = l_Lean_MessageData_ofConstName(v_constName_622_, v___x_630_);
v___x_632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_629_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3, &l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3);
v___x_634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v___x_634_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___boxed(lean_object* v_constName_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4(v_constName_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0(lean_object* v_cidx_677_, uint8_t v___x_678_, uint8_t v___x_679_, uint8_t v___x_680_, lean_object* v_ys_681_, lean_object* v_x_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = l_Lean_mkRawNatLit(v_cidx_677_);
v___x_689_ = l_Lean_Meta_mkLambdaFVars(v_ys_681_, v___x_688_, v___x_678_, v___x_679_, v___x_678_, v___x_679_, v___x_680_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0___boxed(lean_object* v_cidx_690_, lean_object* v___x_691_, lean_object* v___x_692_, lean_object* v___x_693_, lean_object* v_ys_694_, lean_object* v_x_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
uint8_t v___x_34830__boxed_701_; uint8_t v___x_34831__boxed_702_; uint8_t v___x_34832__boxed_703_; lean_object* v_res_704_; 
v___x_34830__boxed_701_ = lean_unbox(v___x_691_);
v___x_34831__boxed_702_ = lean_unbox(v___x_692_);
v___x_34832__boxed_703_ = lean_unbox(v___x_693_);
v_res_704_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0(v_cidx_690_, v___x_34830__boxed_701_, v___x_34831__boxed_702_, v___x_34832__boxed_703_, v_ys_694_, v_x_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec_ref(v_x_695_);
lean_dec_ref(v_ys_694_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(uint8_t v___x_705_, lean_object* v___x_706_, lean_object* v_as_x27_707_, lean_object* v_b_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
if (lean_obj_tag(v_as_x27_707_) == 0)
{
lean_object* v___x_714_; 
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v_b_708_);
return v___x_714_;
}
else
{
lean_object* v_head_715_; lean_object* v_tail_716_; lean_object* v___x_717_; 
v_head_715_ = lean_ctor_get(v_as_x27_707_, 0);
lean_inc(v_head_715_);
v_tail_716_ = lean_ctor_get(v_as_x27_707_, 1);
lean_inc(v_tail_716_);
lean_dec_ref(v_as_x27_707_);
v___x_717_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4(v_head_715_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v_toConstantVal_719_; lean_object* v_cidx_720_; lean_object* v_numFields_721_; lean_object* v_type_722_; lean_object* v___x_723_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref(v___x_717_);
v_toConstantVal_719_ = lean_ctor_get(v_a_718_, 0);
lean_inc_ref(v_toConstantVal_719_);
v_cidx_720_ = lean_ctor_get(v_a_718_, 2);
lean_inc(v_cidx_720_);
v_numFields_721_ = lean_ctor_get(v_a_718_, 4);
lean_inc(v_numFields_721_);
lean_dec(v_a_718_);
v_type_722_ = lean_ctor_get(v_toConstantVal_719_, 2);
lean_inc_ref(v_type_722_);
lean_dec_ref(v_toConstantVal_719_);
v___x_723_ = l_Lean_Meta_instantiateForall(v_type_722_, v___x_706_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_741_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_741_ == 0)
{
v___x_726_ = v___x_723_;
v_isShared_727_ = v_isSharedCheck_741_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_723_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_741_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
uint8_t v___x_728_; uint8_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___f_733_; lean_object* v___x_735_; 
v___x_728_ = 0;
v___x_729_ = 1;
v___x_730_ = lean_box(v___x_728_);
v___x_731_ = lean_box(v___x_705_);
v___x_732_ = lean_box(v___x_729_);
v___f_733_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_733_, 0, v_cidx_720_);
lean_closure_set(v___f_733_, 1, v___x_730_);
lean_closure_set(v___f_733_, 2, v___x_731_);
lean_closure_set(v___f_733_, 3, v___x_732_);
if (v_isShared_727_ == 0)
{
lean_ctor_set_tag(v___x_726_, 1);
lean_ctor_set(v___x_726_, 0, v_numFields_721_);
v___x_735_ = v___x_726_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_numFields_721_);
v___x_735_ = v_reuseFailAlloc_740_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(v_a_724_, v___x_735_, v___f_733_, v___x_728_, v___x_728_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_738_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref(v___x_736_);
v___x_738_ = l_Lean_Expr_app___override(v_b_708_, v_a_737_);
v_as_x27_707_ = v_tail_716_;
v_b_708_ = v___x_738_;
goto _start;
}
else
{
lean_dec(v_tail_716_);
lean_dec_ref(v_b_708_);
return v___x_736_;
}
}
}
}
else
{
lean_dec(v_numFields_721_);
lean_dec(v_cidx_720_);
lean_dec(v_tail_716_);
lean_dec_ref(v_b_708_);
return v___x_723_;
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec(v_tail_716_);
lean_dec_ref(v_b_708_);
v_a_742_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_717_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_717_);
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
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___boxed(lean_object* v___x_750_, lean_object* v___x_751_, lean_object* v_as_x27_752_, lean_object* v_b_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
uint8_t v___x_34861__boxed_759_; lean_object* v_res_760_; 
v___x_34861__boxed_759_ = lean_unbox(v___x_750_);
v_res_760_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(v___x_34861__boxed_759_, v___x_751_, v_as_x27_752_, v_b_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec_ref(v___x_751_);
return v_res_760_;
}
}
static lean_object* _init_l_mkCtorIdx___lam__0___closed__0(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_box(0);
v___x_762_ = l_Lean_Level_succ___override(v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__0(lean_object* v_xs_763_, uint8_t v___x_764_, uint8_t v___x_765_, uint8_t v___x_766_, lean_object* v_val_767_, lean_object* v___x_768_, lean_object* v___x_769_, lean_object* v___x_770_, lean_object* v___x_771_, lean_object* v___x_772_, lean_object* v_ctors_773_, lean_object* v___x_774_, lean_object* v_x_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_value_782_; lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_785_ = l_Lean_InductiveVal_numCtors(v_val_767_);
v___x_786_ = lean_unsigned_to_nat(1u);
v___x_787_ = lean_nat_dec_eq(v___x_785_, v___x_786_);
lean_dec(v___x_785_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; 
lean_dec(v___x_774_);
lean_inc_ref(v_x_775_);
lean_inc_ref(v___x_768_);
v___x_788_ = lean_array_push(v___x_768_, v_x_775_);
v___x_789_ = l_Lean_Meta_mkLambdaFVars(v___x_788_, v___x_769_, v___x_764_, v___x_765_, v___x_764_, v___x_765_, v___x_766_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec_ref(v___x_788_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref(v___x_789_);
v___x_791_ = lean_obj_once(&l_mkCtorIdx___lam__0___closed__0, &l_mkCtorIdx___lam__0___closed__0_once, _init_l_mkCtorIdx___lam__0___closed__0);
v___x_792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v___x_770_);
v___x_793_ = l_Lean_mkConst(v___x_771_, v___x_792_);
v___x_794_ = l_Lean_mkAppN(v___x_793_, v___x_772_);
v___x_795_ = l_Lean_Expr_app___override(v___x_794_, v_a_790_);
v___x_796_ = l_Lean_mkAppN(v___x_795_, v___x_768_);
lean_dec_ref(v___x_768_);
lean_inc_ref(v_x_775_);
v___x_797_ = l_Lean_Expr_app___override(v___x_796_, v_x_775_);
v___x_798_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(v___x_765_, v___x_772_, v_ctors_773_, v___x_797_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref(v___x_798_);
v_value_782_ = v_a_799_;
goto v___jp_781_;
}
else
{
lean_dec_ref(v_x_775_);
lean_dec_ref(v_xs_763_);
return v___x_798_;
}
}
else
{
lean_dec_ref(v_x_775_);
lean_dec(v_ctors_773_);
lean_dec(v___x_771_);
lean_dec(v___x_770_);
lean_dec_ref(v___x_768_);
lean_dec_ref(v_xs_763_);
return v___x_789_;
}
}
else
{
lean_object* v___x_800_; 
lean_dec(v_ctors_773_);
lean_dec(v___x_771_);
lean_dec(v___x_770_);
lean_dec_ref(v___x_769_);
lean_dec_ref(v___x_768_);
v___x_800_ = l_Lean_mkRawNatLit(v___x_774_);
v_value_782_ = v___x_800_;
goto v___jp_781_;
}
v___jp_781_:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_array_push(v_xs_763_, v_x_775_);
v___x_784_ = l_Lean_Meta_mkLambdaFVars(v___x_783_, v_value_782_, v___x_764_, v___x_765_, v___x_764_, v___x_765_, v___x_766_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec_ref(v___x_783_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__0___boxed(lean_object** _args){
lean_object* v_xs_801_ = _args[0];
lean_object* v___x_802_ = _args[1];
lean_object* v___x_803_ = _args[2];
lean_object* v___x_804_ = _args[3];
lean_object* v_val_805_ = _args[4];
lean_object* v___x_806_ = _args[5];
lean_object* v___x_807_ = _args[6];
lean_object* v___x_808_ = _args[7];
lean_object* v___x_809_ = _args[8];
lean_object* v___x_810_ = _args[9];
lean_object* v_ctors_811_ = _args[10];
lean_object* v___x_812_ = _args[11];
lean_object* v_x_813_ = _args[12];
lean_object* v___y_814_ = _args[13];
lean_object* v___y_815_ = _args[14];
lean_object* v___y_816_ = _args[15];
lean_object* v___y_817_ = _args[16];
lean_object* v___y_818_ = _args[17];
_start:
{
uint8_t v___x_34952__boxed_819_; uint8_t v___x_34953__boxed_820_; uint8_t v___x_34954__boxed_821_; lean_object* v_res_822_; 
v___x_34952__boxed_819_ = lean_unbox(v___x_802_);
v___x_34953__boxed_820_ = lean_unbox(v___x_803_);
v___x_34954__boxed_821_ = lean_unbox(v___x_804_);
v_res_822_ = l_mkCtorIdx___lam__0(v_xs_801_, v___x_34952__boxed_819_, v___x_34953__boxed_820_, v___x_34954__boxed_821_, v_val_805_, v___x_806_, v___x_807_, v___x_808_, v___x_809_, v___x_810_, v_ctors_811_, v___x_812_, v_x_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec_ref(v___x_810_);
lean_dec_ref(v_val_805_);
return v_res_822_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_823_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0);
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_826_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1);
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
lean_ctor_set(v___x_828_, 2, v___x_827_);
lean_ctor_set(v___x_828_, 3, v___x_827_);
lean_ctor_set(v___x_828_, 4, v___x_826_);
lean_ctor_set(v___x_828_, 5, v___x_826_);
lean_ctor_set(v___x_828_, 6, v___x_826_);
lean_ctor_set(v___x_828_, 7, v___x_826_);
lean_ctor_set(v___x_828_, 8, v___x_826_);
lean_ctor_set(v___x_828_, 9, v___x_826_);
return v___x_828_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = lean_unsigned_to_nat(32u);
v___x_830_ = lean_mk_empty_array_with_capacity(v___x_829_);
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4(void){
_start:
{
size_t v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_832_ = ((size_t)5ULL);
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = lean_unsigned_to_nat(32u);
v___x_835_ = lean_mk_empty_array_with_capacity(v___x_834_);
v___x_836_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3);
v___x_837_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v___x_835_);
lean_ctor_set(v___x_837_, 2, v___x_833_);
lean_ctor_set(v___x_837_, 3, v___x_833_);
lean_ctor_set_usize(v___x_837_, 4, v___x_832_);
return v___x_837_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_838_ = lean_box(1);
v___x_839_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4);
v___x_840_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1);
v___x_841_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_841_, 0, v___x_840_);
lean_ctor_set(v___x_841_, 1, v___x_839_);
lean_ctor_set(v___x_841_, 2, v___x_838_);
return v___x_841_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6));
v___x_844_ = l_Lean_stringToMessageData(v___x_843_);
return v___x_844_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8));
v___x_847_ = l_Lean_stringToMessageData(v___x_846_);
return v___x_847_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10));
v___x_850_ = l_Lean_stringToMessageData(v___x_849_);
return v___x_850_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12));
v___x_853_ = l_Lean_stringToMessageData(v___x_852_);
return v___x_853_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14));
v___x_856_ = l_Lean_stringToMessageData(v___x_855_);
return v___x_856_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16));
v___x_859_ = l_Lean_stringToMessageData(v___x_858_);
return v___x_859_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18));
v___x_862_ = l_Lean_stringToMessageData(v___x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(lean_object* v_msg_863_, lean_object* v_declHint_864_, lean_object* v___y_865_){
_start:
{
lean_object* v___x_867_; lean_object* v_env_868_; uint8_t v___x_869_; 
v___x_867_ = lean_st_ref_get(v___y_865_);
v_env_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc_ref(v_env_868_);
lean_dec(v___x_867_);
v___x_869_ = l_Lean_Name_isAnonymous(v_declHint_864_);
if (v___x_869_ == 0)
{
uint8_t v_isExporting_870_; 
v_isExporting_870_ = lean_ctor_get_uint8(v_env_868_, sizeof(void*)*8);
if (v_isExporting_870_ == 0)
{
lean_object* v___x_871_; 
lean_dec_ref(v_env_868_);
lean_dec(v_declHint_864_);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v_msg_863_);
return v___x_871_;
}
else
{
lean_object* v___x_872_; uint8_t v___x_873_; 
lean_inc_ref(v_env_868_);
v___x_872_ = l_Lean_Environment_setExporting(v_env_868_, v___x_869_);
lean_inc(v_declHint_864_);
lean_inc_ref(v___x_872_);
v___x_873_ = l_Lean_Environment_contains(v___x_872_, v_declHint_864_, v_isExporting_870_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
lean_dec_ref(v___x_872_);
lean_dec_ref(v_env_868_);
lean_dec(v_declHint_864_);
v___x_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_874_, 0, v_msg_863_);
return v___x_874_;
}
else
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v_c_880_; lean_object* v___x_881_; 
v___x_875_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2);
v___x_876_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5);
v___x_877_ = l_Lean_Options_empty;
v___x_878_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_878_, 0, v___x_872_);
lean_ctor_set(v___x_878_, 1, v___x_875_);
lean_ctor_set(v___x_878_, 2, v___x_876_);
lean_ctor_set(v___x_878_, 3, v___x_877_);
lean_inc(v_declHint_864_);
v___x_879_ = l_Lean_MessageData_ofConstName(v_declHint_864_, v___x_869_);
v_c_880_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_880_, 0, v___x_878_);
lean_ctor_set(v_c_880_, 1, v___x_879_);
v___x_881_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_868_, v_declHint_864_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
lean_dec_ref(v_env_868_);
lean_dec(v_declHint_864_);
v___x_882_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7);
v___x_883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
lean_ctor_set(v___x_883_, 1, v_c_880_);
v___x_884_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9);
v___x_885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_883_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = l_Lean_MessageData_note(v___x_885_);
v___x_887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_887_, 0, v_msg_863_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
return v___x_888_;
}
else
{
lean_object* v_val_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_924_; 
v_val_889_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_924_ == 0)
{
v___x_891_ = v___x_881_;
v_isShared_892_ = v_isSharedCheck_924_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_val_889_);
lean_dec(v___x_881_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_924_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v_mod_896_; uint8_t v___x_897_; 
v___x_893_ = lean_box(0);
v___x_894_ = l_Lean_Environment_header(v_env_868_);
lean_dec_ref(v_env_868_);
v___x_895_ = l_Lean_EnvironmentHeader_moduleNames(v___x_894_);
v_mod_896_ = lean_array_get(v___x_893_, v___x_895_, v_val_889_);
lean_dec(v_val_889_);
lean_dec_ref(v___x_895_);
v___x_897_ = l_Lean_isPrivateName(v_declHint_864_);
lean_dec(v_declHint_864_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_898_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11);
v___x_899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
lean_ctor_set(v___x_899_, 1, v_c_880_);
v___x_900_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13);
v___x_901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = l_Lean_MessageData_ofName(v_mod_896_);
v___x_903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15);
v___x_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = l_Lean_MessageData_note(v___x_905_);
v___x_907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_907_, 0, v_msg_863_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
if (v_isShared_892_ == 0)
{
lean_ctor_set_tag(v___x_891_, 0);
lean_ctor_set(v___x_891_, 0, v___x_907_);
v___x_909_ = v___x_891_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_911_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7);
v___x_912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v_c_880_);
v___x_913_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17);
v___x_914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_912_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = l_Lean_MessageData_ofName(v_mod_896_);
v___x_916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_914_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19);
v___x_918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = l_Lean_MessageData_note(v___x_918_);
v___x_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_920_, 0, v_msg_863_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
if (v_isShared_892_ == 0)
{
lean_ctor_set_tag(v___x_891_, 0);
lean_ctor_set(v___x_891_, 0, v___x_920_);
v___x_922_ = v___x_891_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_925_; 
lean_dec_ref(v_env_868_);
lean_dec(v_declHint_864_);
v___x_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_925_, 0, v_msg_863_);
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___boxed(lean_object* v_msg_926_, lean_object* v_declHint_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_926_, v_declHint_927_, v___y_928_);
lean_dec(v___y_928_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(lean_object* v_msg_931_, lean_object* v_declHint_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v___x_938_; lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_948_; 
v___x_938_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_931_, v_declHint_932_, v___y_936_);
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_948_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_948_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_948_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_943_ = l_Lean_unknownIdentifierMessageTag;
v___x_944_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v_a_939_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_944_);
v___x_946_ = v___x_941_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26___boxed(lean_object* v_msg_949_, lean_object* v_declHint_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(v_msg_949_, v_declHint_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(lean_object* v_ref_957_, lean_object* v_msg_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_fileName_964_; lean_object* v_fileMap_965_; lean_object* v_options_966_; lean_object* v_currRecDepth_967_; lean_object* v_maxRecDepth_968_; lean_object* v_ref_969_; lean_object* v_currNamespace_970_; lean_object* v_openDecls_971_; lean_object* v_initHeartbeats_972_; lean_object* v_maxHeartbeats_973_; lean_object* v_quotContext_974_; lean_object* v_currMacroScope_975_; uint8_t v_diag_976_; lean_object* v_cancelTk_x3f_977_; uint8_t v_suppressElabErrors_978_; lean_object* v_inheritedTraceOptions_979_; lean_object* v_ref_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v_fileName_964_ = lean_ctor_get(v___y_961_, 0);
v_fileMap_965_ = lean_ctor_get(v___y_961_, 1);
v_options_966_ = lean_ctor_get(v___y_961_, 2);
v_currRecDepth_967_ = lean_ctor_get(v___y_961_, 3);
v_maxRecDepth_968_ = lean_ctor_get(v___y_961_, 4);
v_ref_969_ = lean_ctor_get(v___y_961_, 5);
v_currNamespace_970_ = lean_ctor_get(v___y_961_, 6);
v_openDecls_971_ = lean_ctor_get(v___y_961_, 7);
v_initHeartbeats_972_ = lean_ctor_get(v___y_961_, 8);
v_maxHeartbeats_973_ = lean_ctor_get(v___y_961_, 9);
v_quotContext_974_ = lean_ctor_get(v___y_961_, 10);
v_currMacroScope_975_ = lean_ctor_get(v___y_961_, 11);
v_diag_976_ = lean_ctor_get_uint8(v___y_961_, sizeof(void*)*14);
v_cancelTk_x3f_977_ = lean_ctor_get(v___y_961_, 12);
v_suppressElabErrors_978_ = lean_ctor_get_uint8(v___y_961_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_979_ = lean_ctor_get(v___y_961_, 13);
v_ref_980_ = l_Lean_replaceRef(v_ref_957_, v_ref_969_);
lean_inc_ref(v_inheritedTraceOptions_979_);
lean_inc(v_cancelTk_x3f_977_);
lean_inc(v_currMacroScope_975_);
lean_inc(v_quotContext_974_);
lean_inc(v_maxHeartbeats_973_);
lean_inc(v_initHeartbeats_972_);
lean_inc(v_openDecls_971_);
lean_inc(v_currNamespace_970_);
lean_inc(v_maxRecDepth_968_);
lean_inc(v_currRecDepth_967_);
lean_inc_ref(v_options_966_);
lean_inc_ref(v_fileMap_965_);
lean_inc_ref(v_fileName_964_);
v___x_981_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_981_, 0, v_fileName_964_);
lean_ctor_set(v___x_981_, 1, v_fileMap_965_);
lean_ctor_set(v___x_981_, 2, v_options_966_);
lean_ctor_set(v___x_981_, 3, v_currRecDepth_967_);
lean_ctor_set(v___x_981_, 4, v_maxRecDepth_968_);
lean_ctor_set(v___x_981_, 5, v_ref_980_);
lean_ctor_set(v___x_981_, 6, v_currNamespace_970_);
lean_ctor_set(v___x_981_, 7, v_openDecls_971_);
lean_ctor_set(v___x_981_, 8, v_initHeartbeats_972_);
lean_ctor_set(v___x_981_, 9, v_maxHeartbeats_973_);
lean_ctor_set(v___x_981_, 10, v_quotContext_974_);
lean_ctor_set(v___x_981_, 11, v_currMacroScope_975_);
lean_ctor_set(v___x_981_, 12, v_cancelTk_x3f_977_);
lean_ctor_set(v___x_981_, 13, v_inheritedTraceOptions_979_);
lean_ctor_set_uint8(v___x_981_, sizeof(void*)*14, v_diag_976_);
lean_ctor_set_uint8(v___x_981_, sizeof(void*)*14 + 1, v_suppressElabErrors_978_);
v___x_982_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v_msg_958_, v___y_959_, v___y_960_, v___x_981_, v___y_962_);
lean_dec_ref(v___x_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg___boxed(lean_object* v_ref_983_, lean_object* v_msg_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_983_, v_msg_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v_ref_983_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(lean_object* v_ref_991_, lean_object* v_msg_992_, lean_object* v_declHint_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_999_; lean_object* v_a_1000_; lean_object* v___x_1001_; 
v___x_999_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(v_msg_992_, v_declHint_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref(v___x_999_);
v___x_1001_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_991_, v_a_1000_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg___boxed(lean_object* v_ref_1002_, lean_object* v_msg_1003_, lean_object* v_declHint_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_1002_, v_msg_1003_, v_declHint_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v_ref_1002_);
return v_res_1010_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0));
v___x_1013_ = l_Lean_stringToMessageData(v___x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(lean_object* v_ref_1014_, lean_object* v_constName_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1021_; uint8_t v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1021_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1);
v___x_1022_ = 0;
lean_inc(v_constName_1015_);
v___x_1023_ = l_Lean_MessageData_ofConstName(v_constName_1015_, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1021_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_1014_, v___x_1026_, v_constName_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1028_, lean_object* v_constName_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1028_, v_constName_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v_ref_1028_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(lean_object* v_constName_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v_ref_1042_; lean_object* v___x_1043_; 
v_ref_1042_ = lean_ctor_get(v___y_1039_, 5);
v___x_1043_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1042_, v_constName_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg___boxed(lean_object* v_constName_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(v_constName_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(lean_object* v_constName_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v___x_1057_; lean_object* v_env_1058_; uint8_t v___x_1059_; lean_object* v___x_1060_; 
v___x_1057_ = lean_st_ref_get(v___y_1055_);
v_env_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc_ref(v_env_1058_);
lean_dec(v___x_1057_);
v___x_1059_ = 0;
lean_inc(v_constName_1051_);
v___x_1060_ = l_Lean_Environment_find_x3f(v_env_1058_, v_constName_1051_, v___x_1059_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(v_constName_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
return v___x_1061_;
}
else
{
lean_object* v_val_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec(v_constName_1051_);
v_val_1062_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1060_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_val_1062_);
lean_dec(v___x_1060_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
lean_ctor_set_tag(v___x_1064_, 0);
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_val_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00mkCtorIdx_spec__2___boxed(lean_object* v_constName_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v_constName_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(uint8_t v___x_1077_, lean_object* v_x_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
if (lean_obj_tag(v_x_1078_) == 0)
{
uint8_t v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1084_ = 1;
v___x_1085_ = lean_box(v___x_1084_);
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
return v___x_1086_;
}
else
{
lean_object* v_head_1087_; lean_object* v_tail_1088_; lean_object* v___x_1089_; 
v_head_1087_ = lean_ctor_get(v_x_1078_, 0);
lean_inc(v_head_1087_);
v_tail_1088_ = lean_ctor_get(v_x_1078_, 1);
lean_inc(v_tail_1088_);
lean_dec_ref(v_x_1078_);
v___x_1089_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v_head_1087_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1110_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1110_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1110_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___y_1095_; uint8_t v_a_1096_; 
if (lean_obj_tag(v_a_1090_) == 6)
{
lean_object* v_val_1098_; lean_object* v_numFields_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1104_; 
v_val_1098_ = lean_ctor_get(v_a_1090_, 0);
lean_inc_ref(v_val_1098_);
lean_dec_ref(v_a_1090_);
v_numFields_1099_ = lean_ctor_get(v_val_1098_, 4);
lean_inc(v_numFields_1099_);
lean_dec_ref(v_val_1098_);
v___x_1100_ = lean_unsigned_to_nat(0u);
v___x_1101_ = lean_nat_dec_eq(v_numFields_1099_, v___x_1100_);
lean_dec(v_numFields_1099_);
v___x_1102_ = lean_box(v___x_1101_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1102_);
v___x_1104_ = v___x_1092_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
v___y_1095_ = v___x_1104_;
v_a_1096_ = v___x_1101_;
goto v___jp_1094_;
}
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1108_; 
lean_dec(v_a_1090_);
v___x_1106_ = lean_box(v___x_1077_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1106_);
v___x_1108_ = v___x_1092_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
v___y_1095_ = v___x_1108_;
v_a_1096_ = v___x_1077_;
goto v___jp_1094_;
}
}
v___jp_1094_:
{
if (v_a_1096_ == 0)
{
lean_dec(v_tail_1088_);
return v___y_1095_;
}
else
{
lean_dec_ref(v___y_1095_);
v_x_1078_ = v_tail_1088_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec(v_tail_1088_);
v_a_1111_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1089_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1089_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13___boxed(lean_object* v___x_1119_, lean_object* v_x_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
uint8_t v___x_35472__boxed_1126_; lean_object* v_res_1127_; 
v___x_35472__boxed_1126_ = lean_unbox(v___x_1119_);
v_res_1127_ = l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(v___x_35472__boxed_1126_, v_x_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00mkCtorIdx_spec__9(lean_object* v_declName_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v_declName_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1190_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1137_ = v___x_1134_;
v_isShared_1138_ = v_isSharedCheck_1190_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1134_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1190_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
if (lean_obj_tag(v_a_1135_) == 5)
{
lean_object* v_val_1139_; lean_object* v_toConstantVal_1140_; lean_object* v_numParams_1141_; lean_object* v_numIndices_1142_; lean_object* v_ctors_1143_; uint8_t v_isRec_1144_; uint8_t v_isUnsafe_1145_; lean_object* v_type_1146_; uint8_t v___x_1147_; 
v_val_1139_ = lean_ctor_get(v_a_1135_, 0);
lean_inc_ref(v_val_1139_);
lean_dec_ref(v_a_1135_);
v_toConstantVal_1140_ = lean_ctor_get(v_val_1139_, 0);
v_numParams_1141_ = lean_ctor_get(v_val_1139_, 1);
lean_inc(v_numParams_1141_);
v_numIndices_1142_ = lean_ctor_get(v_val_1139_, 2);
lean_inc(v_numIndices_1142_);
v_ctors_1143_ = lean_ctor_get(v_val_1139_, 4);
lean_inc(v_ctors_1143_);
v_isRec_1144_ = lean_ctor_get_uint8(v_val_1139_, sizeof(void*)*6);
v_isUnsafe_1145_ = lean_ctor_get_uint8(v_val_1139_, sizeof(void*)*6 + 1);
v_type_1146_ = lean_ctor_get(v_toConstantVal_1140_, 2);
v___x_1147_ = l_Lean_Expr_isProp(v_type_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v___x_1148_ = l_Lean_InductiveVal_numTypeFormers(v_val_1139_);
lean_dec_ref(v_val_1139_);
v___x_1149_ = lean_unsigned_to_nat(1u);
v___x_1150_ = lean_nat_dec_eq(v___x_1148_, v___x_1149_);
lean_dec(v___x_1148_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
lean_dec(v_ctors_1143_);
lean_dec(v_numIndices_1142_);
lean_dec(v_numParams_1141_);
v___x_1151_ = lean_box(v___x_1150_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1151_);
v___x_1153_ = v___x_1137_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
else
{
lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = lean_unsigned_to_nat(0u);
v___x_1156_ = lean_nat_dec_eq(v_numIndices_1142_, v___x_1155_);
lean_dec(v_numIndices_1142_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; lean_object* v___x_1159_; 
lean_dec(v_ctors_1143_);
lean_dec(v_numParams_1141_);
v___x_1157_ = lean_box(v___x_1156_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1157_);
v___x_1159_ = v___x_1137_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
else
{
uint8_t v___x_1161_; 
v___x_1161_ = lean_nat_dec_eq(v_numParams_1141_, v___x_1155_);
lean_dec(v_numParams_1141_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; lean_object* v___x_1164_; 
lean_dec(v_ctors_1143_);
v___x_1162_ = lean_box(v___x_1161_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1162_);
v___x_1164_ = v___x_1137_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
else
{
uint8_t v___x_1166_; 
v___x_1166_ = l_List_isEmpty___redArg(v_ctors_1143_);
if (v___x_1166_ == 0)
{
if (v_isRec_1144_ == 0)
{
if (v_isUnsafe_1145_ == 0)
{
lean_object* v___x_1167_; 
lean_del_object(v___x_1137_);
v___x_1167_ = l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(v_isUnsafe_1145_, v_ctors_1143_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
return v___x_1167_;
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1170_; 
lean_dec(v_ctors_1143_);
v___x_1168_ = lean_box(v_isRec_1144_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1168_);
v___x_1170_ = v___x_1137_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
else
{
lean_object* v___x_1172_; lean_object* v___x_1174_; 
lean_dec(v_ctors_1143_);
v___x_1172_ = lean_box(v___x_1166_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1172_);
v___x_1174_ = v___x_1137_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
else
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
lean_dec(v_ctors_1143_);
v___x_1176_ = lean_box(v___x_1147_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1176_);
v___x_1178_ = v___x_1137_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
}
else
{
uint8_t v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
lean_dec(v_ctors_1143_);
lean_dec(v_numIndices_1142_);
lean_dec(v_numParams_1141_);
lean_dec_ref(v_val_1139_);
v___x_1180_ = 0;
v___x_1181_ = lean_box(v___x_1180_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1181_);
v___x_1183_ = v___x_1137_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
else
{
uint8_t v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1188_; 
lean_dec(v_a_1135_);
v___x_1185_ = 0;
v___x_1186_ = lean_box(v___x_1185_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1186_);
v___x_1188_ = v___x_1137_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1186_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
v_a_1191_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1134_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1134_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00mkCtorIdx_spec__9___boxed(lean_object* v_declName_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_isEnumType___at___00mkCtorIdx_spec__9(v_declName_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0(lean_object* v_k_1206_, lean_object* v_b_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v___x_1213_; 
lean_inc(v___y_1211_);
lean_inc_ref(v___y_1210_);
lean_inc(v___y_1209_);
lean_inc_ref(v___y_1208_);
v___x_1213_ = lean_apply_6(v_k_1206_, v_b_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, lean_box(0));
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(lean_object* v_k_1214_, lean_object* v_b_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0(v_k_1214_, v_b_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(lean_object* v_name_1222_, uint8_t v_bi_1223_, lean_object* v_type_1224_, lean_object* v_k_1225_, uint8_t v_kind_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v___f_1232_; lean_object* v___x_1233_; 
v___f_1232_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1232_, 0, v_k_1225_);
v___x_1233_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1222_, v_bi_1223_, v_type_1224_, v___f_1232_, v_kind_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1233_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1233_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
v_a_1242_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1233_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1233_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___boxed(lean_object* v_name_1250_, lean_object* v_bi_1251_, lean_object* v_type_1252_, lean_object* v_k_1253_, lean_object* v_kind_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
uint8_t v_bi_boxed_1260_; uint8_t v_kind_boxed_1261_; lean_object* v_res_1262_; 
v_bi_boxed_1260_ = lean_unbox(v_bi_1251_);
v_kind_boxed_1261_ = lean_unbox(v_kind_1254_);
v_res_1262_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(v_name_1250_, v_bi_boxed_1260_, v_type_1252_, v_k_1253_, v_kind_boxed_1261_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(lean_object* v_name_1263_, lean_object* v_type_1264_, lean_object* v_k_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
uint8_t v___x_1271_; uint8_t v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = 0;
v___x_1272_ = 0;
v___x_1273_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(v_name_1263_, v___x_1271_, v_type_1264_, v_k_1265_, v___x_1272_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg___boxed(lean_object* v_name_1274_, lean_object* v_type_1275_, lean_object* v_k_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(v_name_1274_, v_type_1275_, v_k_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(lean_object* v_env_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; lean_object* v_nextMacroScope_1288_; lean_object* v_ngen_1289_; lean_object* v_auxDeclNGen_1290_; lean_object* v_traceState_1291_; lean_object* v_messages_1292_; lean_object* v_infoState_1293_; lean_object* v_snapshotTasks_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1320_; 
v___x_1287_ = lean_st_ref_take(v___y_1285_);
v_nextMacroScope_1288_ = lean_ctor_get(v___x_1287_, 1);
v_ngen_1289_ = lean_ctor_get(v___x_1287_, 2);
v_auxDeclNGen_1290_ = lean_ctor_get(v___x_1287_, 3);
v_traceState_1291_ = lean_ctor_get(v___x_1287_, 4);
v_messages_1292_ = lean_ctor_get(v___x_1287_, 6);
v_infoState_1293_ = lean_ctor_get(v___x_1287_, 7);
v_snapshotTasks_1294_ = lean_ctor_get(v___x_1287_, 8);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1320_ == 0)
{
lean_object* v_unused_1321_; lean_object* v_unused_1322_; 
v_unused_1321_ = lean_ctor_get(v___x_1287_, 5);
lean_dec(v_unused_1321_);
v_unused_1322_ = lean_ctor_get(v___x_1287_, 0);
lean_dec(v_unused_1322_);
v___x_1296_ = v___x_1287_;
v_isShared_1297_ = v_isSharedCheck_1320_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_snapshotTasks_1294_);
lean_inc(v_infoState_1293_);
lean_inc(v_messages_1292_);
lean_inc(v_traceState_1291_);
lean_inc(v_auxDeclNGen_1290_);
lean_inc(v_ngen_1289_);
lean_inc(v_nextMacroScope_1288_);
lean_dec(v___x_1287_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1320_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; lean_object* v___x_1300_; 
v___x_1298_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 5, v___x_1298_);
lean_ctor_set(v___x_1296_, 0, v_env_1283_);
v___x_1300_ = v___x_1296_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_env_1283_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_nextMacroScope_1288_);
lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_ngen_1289_);
lean_ctor_set(v_reuseFailAlloc_1319_, 3, v_auxDeclNGen_1290_);
lean_ctor_set(v_reuseFailAlloc_1319_, 4, v_traceState_1291_);
lean_ctor_set(v_reuseFailAlloc_1319_, 5, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1319_, 6, v_messages_1292_);
lean_ctor_set(v_reuseFailAlloc_1319_, 7, v_infoState_1293_);
lean_ctor_set(v_reuseFailAlloc_1319_, 8, v_snapshotTasks_1294_);
v___x_1300_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v_mctx_1303_; lean_object* v_zetaDeltaFVarIds_1304_; lean_object* v_postponed_1305_; lean_object* v_diag_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1317_; 
v___x_1301_ = lean_st_ref_set(v___y_1285_, v___x_1300_);
v___x_1302_ = lean_st_ref_take(v___y_1284_);
v_mctx_1303_ = lean_ctor_get(v___x_1302_, 0);
v_zetaDeltaFVarIds_1304_ = lean_ctor_get(v___x_1302_, 2);
v_postponed_1305_ = lean_ctor_get(v___x_1302_, 3);
v_diag_1306_ = lean_ctor_get(v___x_1302_, 4);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1317_ == 0)
{
lean_object* v_unused_1318_; 
v_unused_1318_ = lean_ctor_get(v___x_1302_, 1);
lean_dec(v_unused_1318_);
v___x_1308_ = v___x_1302_;
v_isShared_1309_ = v_isSharedCheck_1317_;
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
v_isShared_1309_ = v_isSharedCheck_1317_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1310_; lean_object* v___x_1312_; 
v___x_1310_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 1, v___x_1310_);
v___x_1312_ = v___x_1308_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_mctx_1303_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v___x_1310_);
lean_ctor_set(v_reuseFailAlloc_1316_, 2, v_zetaDeltaFVarIds_1304_);
lean_ctor_set(v_reuseFailAlloc_1316_, 3, v_postponed_1305_);
lean_ctor_set(v_reuseFailAlloc_1316_, 4, v_diag_1306_);
v___x_1312_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = lean_st_ref_set(v___y_1284_, v___x_1312_);
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
return v___x_1315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg___boxed(lean_object* v_env_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(v_env_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec(v___y_1324_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(lean_object* v_declName_1328_, lean_object* v_entry_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v___x_1335_; lean_object* v_env_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1335_ = lean_st_ref_get(v___y_1333_);
v_env_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc_ref(v_env_1336_);
lean_dec(v___x_1335_);
v___x_1337_ = l_Lean_Linter_deprecatedAttr;
v___x_1338_ = l_Lean_ParametricAttribute_setParam___redArg(v___x_1337_, v_env_1336_, v_declName_1328_, v_entry_1329_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1348_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1341_ = v___x_1338_;
v_isShared_1342_ = v_isSharedCheck_1348_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1338_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1348_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
lean_ctor_set_tag(v___x_1341_, 3);
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = l_Lean_MessageData_ofFormat(v___x_1344_);
v___x_1346_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v___x_1345_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
return v___x_1346_;
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1350_; 
v_a_1349_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1349_);
lean_dec_ref(v___x_1338_);
v___x_1350_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(v_a_1349_, v___y_1331_, v___y_1333_);
return v___x_1350_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11___boxed(lean_object* v_declName_1351_, lean_object* v_entry_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(v_declName_1351_, v_entry_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(lean_object* v_declName_1359_, uint8_t v_s_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v___x_1364_; lean_object* v_env_1365_; lean_object* v_nextMacroScope_1366_; lean_object* v_ngen_1367_; lean_object* v_auxDeclNGen_1368_; lean_object* v_traceState_1369_; lean_object* v_messages_1370_; lean_object* v_infoState_1371_; lean_object* v_snapshotTasks_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1401_; 
v___x_1364_ = lean_st_ref_take(v___y_1362_);
v_env_1365_ = lean_ctor_get(v___x_1364_, 0);
v_nextMacroScope_1366_ = lean_ctor_get(v___x_1364_, 1);
v_ngen_1367_ = lean_ctor_get(v___x_1364_, 2);
v_auxDeclNGen_1368_ = lean_ctor_get(v___x_1364_, 3);
v_traceState_1369_ = lean_ctor_get(v___x_1364_, 4);
v_messages_1370_ = lean_ctor_get(v___x_1364_, 6);
v_infoState_1371_ = lean_ctor_get(v___x_1364_, 7);
v_snapshotTasks_1372_ = lean_ctor_get(v___x_1364_, 8);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; 
v_unused_1402_ = lean_ctor_get(v___x_1364_, 5);
lean_dec(v_unused_1402_);
v___x_1374_ = v___x_1364_;
v_isShared_1375_ = v_isSharedCheck_1401_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_snapshotTasks_1372_);
lean_inc(v_infoState_1371_);
lean_inc(v_messages_1370_);
lean_inc(v_traceState_1369_);
lean_inc(v_auxDeclNGen_1368_);
lean_inc(v_ngen_1367_);
lean_inc(v_nextMacroScope_1366_);
lean_inc(v_env_1365_);
lean_dec(v___x_1364_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1401_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
uint8_t v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1376_ = 0;
v___x_1377_ = lean_box(0);
v___x_1378_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1365_, v_declName_1359_, v_s_1360_, v___x_1376_, v___x_1377_);
v___x_1379_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 5, v___x_1379_);
lean_ctor_set(v___x_1374_, 0, v___x_1378_);
v___x_1381_ = v___x_1374_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_nextMacroScope_1366_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v_ngen_1367_);
lean_ctor_set(v_reuseFailAlloc_1400_, 3, v_auxDeclNGen_1368_);
lean_ctor_set(v_reuseFailAlloc_1400_, 4, v_traceState_1369_);
lean_ctor_set(v_reuseFailAlloc_1400_, 5, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1400_, 6, v_messages_1370_);
lean_ctor_set(v_reuseFailAlloc_1400_, 7, v_infoState_1371_);
lean_ctor_set(v_reuseFailAlloc_1400_, 8, v_snapshotTasks_1372_);
v___x_1381_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v_mctx_1384_; lean_object* v_zetaDeltaFVarIds_1385_; lean_object* v_postponed_1386_; lean_object* v_diag_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1398_; 
v___x_1382_ = lean_st_ref_set(v___y_1362_, v___x_1381_);
v___x_1383_ = lean_st_ref_take(v___y_1361_);
v_mctx_1384_ = lean_ctor_get(v___x_1383_, 0);
v_zetaDeltaFVarIds_1385_ = lean_ctor_get(v___x_1383_, 2);
v_postponed_1386_ = lean_ctor_get(v___x_1383_, 3);
v_diag_1387_ = lean_ctor_get(v___x_1383_, 4);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; 
v_unused_1399_ = lean_ctor_get(v___x_1383_, 1);
lean_dec(v_unused_1399_);
v___x_1389_ = v___x_1383_;
v_isShared_1390_ = v_isSharedCheck_1398_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_diag_1387_);
lean_inc(v_postponed_1386_);
lean_inc(v_zetaDeltaFVarIds_1385_);
lean_inc(v_mctx_1384_);
lean_dec(v___x_1383_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1398_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1391_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 1, v___x_1391_);
v___x_1393_ = v___x_1389_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_mctx_1384_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1397_, 2, v_zetaDeltaFVarIds_1385_);
lean_ctor_set(v_reuseFailAlloc_1397_, 3, v_postponed_1386_);
lean_ctor_set(v_reuseFailAlloc_1397_, 4, v_diag_1387_);
v___x_1393_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1394_ = lean_st_ref_set(v___y_1361_, v___x_1393_);
v___x_1395_ = lean_box(0);
v___x_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
return v___x_1396_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg___boxed(lean_object* v_declName_1403_, lean_object* v_s_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
uint8_t v_s_boxed_1408_; lean_object* v_res_1409_; 
v_s_boxed_1408_ = lean_unbox(v_s_1404_);
v_res_1409_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(v_declName_1403_, v_s_boxed_1408_, v___y_1405_, v___y_1406_);
lean_dec(v___y_1406_);
lean_dec(v___y_1405_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(lean_object* v_declName_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
uint8_t v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = 0;
v___x_1417_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(v_declName_1410_, v___x_1416_, v___y_1412_, v___y_1414_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10___boxed(lean_object* v_declName_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(v_declName_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__1(lean_object* v___x_1431_, lean_object* v___x_1432_, lean_object* v_xs_1433_, uint8_t v___x_1434_, uint8_t v___x_1435_, lean_object* v_val_1436_, lean_object* v___x_1437_, lean_object* v___x_1438_, lean_object* v___x_1439_, lean_object* v___x_1440_, lean_object* v_ctors_1441_, lean_object* v___x_1442_, lean_object* v___x_1443_, lean_object* v_levelParams_1444_, lean_object* v_indName_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___x_1542_; 
lean_inc_ref(v___x_1432_);
lean_inc_ref(v___x_1431_);
v___x_1542_ = l_Lean_mkArrow(v___x_1431_, v___x_1432_, v___y_1448_, v___y_1449_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; uint8_t v___x_1544_; lean_object* v___x_1545_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref(v___x_1542_);
v___x_1544_ = 1;
v___x_1545_ = l_Lean_Meta_mkForallFVars(v_xs_1433_, v_a_1543_, v___x_1434_, v___x_1435_, v___x_1435_, v___x_1544_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___f_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref(v___x_1545_);
v___x_1547_ = lean_box(v___x_1434_);
v___x_1548_ = lean_box(v___x_1435_);
v___x_1549_ = lean_box(v___x_1544_);
lean_inc(v___x_1438_);
lean_inc_ref(v_val_1436_);
v___f_1550_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1550_, 0, v_xs_1433_);
lean_closure_set(v___f_1550_, 1, v___x_1547_);
lean_closure_set(v___f_1550_, 2, v___x_1548_);
lean_closure_set(v___f_1550_, 3, v___x_1549_);
lean_closure_set(v___f_1550_, 4, v_val_1436_);
lean_closure_set(v___f_1550_, 5, v___x_1437_);
lean_closure_set(v___f_1550_, 6, v___x_1432_);
lean_closure_set(v___f_1550_, 7, v___x_1438_);
lean_closure_set(v___f_1550_, 8, v___x_1439_);
lean_closure_set(v___f_1550_, 9, v___x_1440_);
lean_closure_set(v___f_1550_, 10, v_ctors_1441_);
lean_closure_set(v___f_1550_, 11, v___x_1442_);
v___x_1551_ = ((lean_object*)(l_mkCtorIdx___lam__1___closed__3));
v___x_1552_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(v___x_1551_, v___x_1431_, v___f_1550_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1554_; lean_object* v_env_1555_; uint32_t v___x_1556_; uint32_t v___x_1557_; uint32_t v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1762_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc_n(v_a_1553_, 2);
lean_dec_ref(v___x_1552_);
v___x_1554_ = lean_st_ref_get(v___y_1449_);
v_env_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc_ref(v_env_1555_);
lean_dec(v___x_1554_);
v___x_1556_ = l_Lean_getMaxHeight(v_env_1555_, v_a_1553_);
v___x_1557_ = 1;
v___x_1558_ = lean_uint32_add(v___x_1556_, v___x_1557_);
v___x_1559_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_1559_, 0, v___x_1558_);
lean_inc(v_a_1546_);
lean_inc(v_levelParams_1444_);
lean_inc(v___x_1443_);
v___x_1560_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(v___x_1443_, v_levelParams_1444_, v_a_1546_, v_a_1553_, v___x_1559_, v___y_1449_);
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1563_ = v___x_1560_;
v_isShared_1564_ = v_isSharedCheck_1762_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1560_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1762_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
lean_ctor_set_tag(v___x_1563_, 1);
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1645_; lean_object* v___y_1646_; lean_object* v___y_1647_; lean_object* v___y_1648_; lean_object* v___x_1687_; 
lean_inc_ref(v___x_1566_);
v___x_1687_ = l_Lean_addDecl(v___x_1566_, v___x_1434_, v___y_1448_, v___y_1449_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v___x_1688_; lean_object* v_env_1689_; lean_object* v_nextMacroScope_1690_; lean_object* v_ngen_1691_; lean_object* v_auxDeclNGen_1692_; lean_object* v_traceState_1693_; lean_object* v_messages_1694_; lean_object* v_infoState_1695_; lean_object* v_snapshotTasks_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1759_; 
lean_dec_ref(v___x_1687_);
v___x_1688_ = lean_st_ref_take(v___y_1449_);
v_env_1689_ = lean_ctor_get(v___x_1688_, 0);
v_nextMacroScope_1690_ = lean_ctor_get(v___x_1688_, 1);
v_ngen_1691_ = lean_ctor_get(v___x_1688_, 2);
v_auxDeclNGen_1692_ = lean_ctor_get(v___x_1688_, 3);
v_traceState_1693_ = lean_ctor_get(v___x_1688_, 4);
v_messages_1694_ = lean_ctor_get(v___x_1688_, 6);
v_infoState_1695_ = lean_ctor_get(v___x_1688_, 7);
v_snapshotTasks_1696_ = lean_ctor_get(v___x_1688_, 8);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1759_ == 0)
{
lean_object* v_unused_1760_; 
v_unused_1760_ = lean_ctor_get(v___x_1688_, 5);
lean_dec(v_unused_1760_);
v___x_1698_ = v___x_1688_;
v_isShared_1699_ = v_isSharedCheck_1759_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_snapshotTasks_1696_);
lean_inc(v_infoState_1695_);
lean_inc(v_messages_1694_);
lean_inc(v_traceState_1693_);
lean_inc(v_auxDeclNGen_1692_);
lean_inc(v_ngen_1691_);
lean_inc(v_nextMacroScope_1690_);
lean_inc(v_env_1689_);
lean_dec(v___x_1688_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1759_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1703_; 
lean_inc(v___x_1443_);
v___x_1700_ = l_Lean_Meta_addToCompletionBlackList(v_env_1689_, v___x_1443_);
v___x_1701_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 5, v___x_1701_);
lean_ctor_set(v___x_1698_, 0, v___x_1700_);
v___x_1703_ = v___x_1698_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1700_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_nextMacroScope_1690_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v_ngen_1691_);
lean_ctor_set(v_reuseFailAlloc_1758_, 3, v_auxDeclNGen_1692_);
lean_ctor_set(v_reuseFailAlloc_1758_, 4, v_traceState_1693_);
lean_ctor_set(v_reuseFailAlloc_1758_, 5, v___x_1701_);
lean_ctor_set(v_reuseFailAlloc_1758_, 6, v_messages_1694_);
lean_ctor_set(v_reuseFailAlloc_1758_, 7, v_infoState_1695_);
lean_ctor_set(v_reuseFailAlloc_1758_, 8, v_snapshotTasks_1696_);
v___x_1703_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v_mctx_1706_; lean_object* v_zetaDeltaFVarIds_1707_; lean_object* v_postponed_1708_; lean_object* v_diag_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1756_; 
v___x_1704_ = lean_st_ref_set(v___y_1449_, v___x_1703_);
v___x_1705_ = lean_st_ref_take(v___y_1447_);
v_mctx_1706_ = lean_ctor_get(v___x_1705_, 0);
v_zetaDeltaFVarIds_1707_ = lean_ctor_get(v___x_1705_, 2);
v_postponed_1708_ = lean_ctor_get(v___x_1705_, 3);
v_diag_1709_ = lean_ctor_get(v___x_1705_, 4);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1756_ == 0)
{
lean_object* v_unused_1757_; 
v_unused_1757_ = lean_ctor_get(v___x_1705_, 1);
lean_dec(v_unused_1757_);
v___x_1711_ = v___x_1705_;
v_isShared_1712_ = v_isSharedCheck_1756_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_diag_1709_);
lean_inc(v_postponed_1708_);
lean_inc(v_zetaDeltaFVarIds_1707_);
lean_inc(v_mctx_1706_);
lean_dec(v___x_1705_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1756_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1713_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 1, v___x_1713_);
v___x_1715_ = v___x_1711_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_mctx_1706_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v___x_1713_);
lean_ctor_set(v_reuseFailAlloc_1755_, 2, v_zetaDeltaFVarIds_1707_);
lean_ctor_set(v_reuseFailAlloc_1755_, 3, v_postponed_1708_);
lean_ctor_set(v_reuseFailAlloc_1755_, 4, v_diag_1709_);
v___x_1715_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v_env_1718_; lean_object* v_nextMacroScope_1719_; lean_object* v_ngen_1720_; lean_object* v_auxDeclNGen_1721_; lean_object* v_traceState_1722_; lean_object* v_messages_1723_; lean_object* v_infoState_1724_; lean_object* v_snapshotTasks_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1753_; 
v___x_1716_ = lean_st_ref_set(v___y_1447_, v___x_1715_);
v___x_1717_ = lean_st_ref_take(v___y_1449_);
v_env_1718_ = lean_ctor_get(v___x_1717_, 0);
v_nextMacroScope_1719_ = lean_ctor_get(v___x_1717_, 1);
v_ngen_1720_ = lean_ctor_get(v___x_1717_, 2);
v_auxDeclNGen_1721_ = lean_ctor_get(v___x_1717_, 3);
v_traceState_1722_ = lean_ctor_get(v___x_1717_, 4);
v_messages_1723_ = lean_ctor_get(v___x_1717_, 6);
v_infoState_1724_ = lean_ctor_get(v___x_1717_, 7);
v_snapshotTasks_1725_ = lean_ctor_get(v___x_1717_, 8);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1753_ == 0)
{
lean_object* v_unused_1754_; 
v_unused_1754_ = lean_ctor_get(v___x_1717_, 5);
lean_dec(v_unused_1754_);
v___x_1727_ = v___x_1717_;
v_isShared_1728_ = v_isSharedCheck_1753_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_snapshotTasks_1725_);
lean_inc(v_infoState_1724_);
lean_inc(v_messages_1723_);
lean_inc(v_traceState_1722_);
lean_inc(v_auxDeclNGen_1721_);
lean_inc(v_ngen_1720_);
lean_inc(v_nextMacroScope_1719_);
lean_inc(v_env_1718_);
lean_dec(v___x_1717_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1753_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
lean_inc(v___x_1443_);
v___x_1729_ = l_Lean_addProtected(v_env_1718_, v___x_1443_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 5, v___x_1701_);
lean_ctor_set(v___x_1727_, 0, v___x_1729_);
v___x_1731_ = v___x_1727_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_nextMacroScope_1719_);
lean_ctor_set(v_reuseFailAlloc_1752_, 2, v_ngen_1720_);
lean_ctor_set(v_reuseFailAlloc_1752_, 3, v_auxDeclNGen_1721_);
lean_ctor_set(v_reuseFailAlloc_1752_, 4, v_traceState_1722_);
lean_ctor_set(v_reuseFailAlloc_1752_, 5, v___x_1701_);
lean_ctor_set(v_reuseFailAlloc_1752_, 6, v_messages_1723_);
lean_ctor_set(v_reuseFailAlloc_1752_, 7, v_infoState_1724_);
lean_ctor_set(v_reuseFailAlloc_1752_, 8, v_snapshotTasks_1725_);
v___x_1731_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v_mctx_1734_; lean_object* v_zetaDeltaFVarIds_1735_; lean_object* v_postponed_1736_; lean_object* v_diag_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1750_; 
v___x_1732_ = lean_st_ref_set(v___y_1449_, v___x_1731_);
v___x_1733_ = lean_st_ref_take(v___y_1447_);
v_mctx_1734_ = lean_ctor_get(v___x_1733_, 0);
v_zetaDeltaFVarIds_1735_ = lean_ctor_get(v___x_1733_, 2);
v_postponed_1736_ = lean_ctor_get(v___x_1733_, 3);
v_diag_1737_ = lean_ctor_get(v___x_1733_, 4);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1750_ == 0)
{
lean_object* v_unused_1751_; 
v_unused_1751_ = lean_ctor_get(v___x_1733_, 1);
lean_dec(v_unused_1751_);
v___x_1739_ = v___x_1733_;
v_isShared_1740_ = v_isSharedCheck_1750_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_diag_1737_);
lean_inc(v_postponed_1736_);
lean_inc(v_zetaDeltaFVarIds_1735_);
lean_inc(v_mctx_1734_);
lean_dec(v___x_1733_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1750_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 1, v___x_1713_);
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_mctx_1734_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v___x_1713_);
lean_ctor_set(v_reuseFailAlloc_1749_, 2, v_zetaDeltaFVarIds_1735_);
lean_ctor_set(v_reuseFailAlloc_1749_, 3, v_postponed_1736_);
lean_ctor_set(v_reuseFailAlloc_1749_, 4, v_diag_1737_);
v___x_1742_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1743_ = lean_st_ref_set(v___y_1447_, v___x_1742_);
v___x_1744_ = lean_unsigned_to_nat(1u);
v___x_1745_ = l_Lean_InductiveVal_numCtors(v_val_1436_);
lean_dec_ref(v_val_1436_);
v___x_1746_ = lean_nat_dec_eq(v___x_1745_, v___x_1744_);
lean_dec(v___x_1745_);
if (v___x_1746_ == 0)
{
v___y_1645_ = v___y_1446_;
v___y_1646_ = v___y_1447_;
v___y_1647_ = v___y_1448_;
v___y_1648_ = v___y_1449_;
goto v___jp_1644_;
}
else
{
uint8_t v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = 2;
lean_inc(v___x_1443_);
v___x_1748_ = l_Lean_Meta_setInlineAttribute(v___x_1443_, v___x_1747_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_dec_ref(v___x_1748_);
v___y_1645_ = v___y_1446_;
v___y_1646_ = v___y_1447_;
v___y_1647_ = v___y_1448_;
v___y_1648_ = v___y_1449_;
goto v___jp_1644_;
}
else
{
lean_dec_ref(v___x_1566_);
lean_dec(v_a_1546_);
lean_dec(v_indName_1445_);
lean_dec(v_levelParams_1444_);
lean_dec(v___x_1443_);
lean_dec(v___x_1438_);
return v___x_1748_;
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
lean_dec_ref(v___x_1566_);
lean_dec(v_a_1546_);
lean_dec(v_indName_1445_);
lean_dec(v_levelParams_1444_);
lean_dec(v___x_1443_);
lean_dec(v___x_1438_);
lean_dec_ref(v_val_1436_);
return v___x_1687_;
}
v___jp_1567_:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Lean_compileDecl(v___x_1566_, v___x_1435_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v___x_1573_; 
lean_dec_ref(v___x_1572_);
lean_inc(v___x_1443_);
v___x_1573_ = l_Lean_enableRealizationsForConst(v___x_1443_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v___x_1574_; 
lean_dec_ref(v___x_1573_);
lean_inc(v_indName_1445_);
v___x_1574_ = l_Lean_isEnumType___at___00mkCtorIdx_spec__9(v_indName_1445_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1635_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1577_ = v___x_1574_;
v_isShared_1578_ = v_isSharedCheck_1635_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1574_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1635_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
uint8_t v___x_1579_; 
v___x_1579_ = lean_unbox(v_a_1575_);
lean_dec(v_a_1575_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; lean_object* v___x_1582_; 
lean_dec(v_a_1546_);
lean_dec(v_indName_1445_);
lean_dec(v_levelParams_1444_);
lean_dec(v___x_1443_);
lean_dec(v___x_1438_);
v___x_1580_ = lean_box(0);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 0, v___x_1580_);
v___x_1582_ = v___x_1577_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1634_; 
lean_del_object(v___x_1577_);
lean_inc(v_indName_1445_);
v___x_1584_ = l_mkToCtorIdxName(v_indName_1445_);
lean_inc(v___x_1443_);
v___x_1585_ = l_Lean_mkConst(v___x_1443_, v___x_1438_);
v___x_1586_ = lean_box(1);
lean_inc(v___x_1584_);
v___x_1587_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(v___x_1584_, v_levelParams_1444_, v_a_1546_, v___x_1585_, v___x_1586_, v___y_1571_);
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1634_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1634_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
lean_ctor_set_tag(v___x_1590_, 1);
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_addDecl(v___x_1593_, v___x_1434_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v___x_1595_; lean_object* v_env_1596_; uint8_t v___x_1597_; 
lean_dec_ref(v___x_1594_);
v___x_1595_ = lean_st_ref_get(v___y_1571_);
v_env_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc_ref(v_env_1596_);
lean_dec(v___x_1595_);
v___x_1597_ = l_Lean_isMarkedMeta(v_env_1596_, v_indName_1445_);
if (v___x_1597_ == 0)
{
v___y_1452_ = v___x_1584_;
v___y_1453_ = v___y_1568_;
v___y_1454_ = v___y_1569_;
v___y_1455_ = v___y_1570_;
v___y_1456_ = v___y_1571_;
goto v___jp_1451_;
}
else
{
lean_object* v___x_1598_; lean_object* v_env_1599_; lean_object* v_nextMacroScope_1600_; lean_object* v_ngen_1601_; lean_object* v_auxDeclNGen_1602_; lean_object* v_traceState_1603_; lean_object* v_messages_1604_; lean_object* v_infoState_1605_; lean_object* v_snapshotTasks_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1631_; 
v___x_1598_ = lean_st_ref_take(v___y_1571_);
v_env_1599_ = lean_ctor_get(v___x_1598_, 0);
v_nextMacroScope_1600_ = lean_ctor_get(v___x_1598_, 1);
v_ngen_1601_ = lean_ctor_get(v___x_1598_, 2);
v_auxDeclNGen_1602_ = lean_ctor_get(v___x_1598_, 3);
v_traceState_1603_ = lean_ctor_get(v___x_1598_, 4);
v_messages_1604_ = lean_ctor_get(v___x_1598_, 6);
v_infoState_1605_ = lean_ctor_get(v___x_1598_, 7);
v_snapshotTasks_1606_ = lean_ctor_get(v___x_1598_, 8);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1631_ == 0)
{
lean_object* v_unused_1632_; 
v_unused_1632_ = lean_ctor_get(v___x_1598_, 5);
lean_dec(v_unused_1632_);
v___x_1608_ = v___x_1598_;
v_isShared_1609_ = v_isSharedCheck_1631_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_snapshotTasks_1606_);
lean_inc(v_infoState_1605_);
lean_inc(v_messages_1604_);
lean_inc(v_traceState_1603_);
lean_inc(v_auxDeclNGen_1602_);
lean_inc(v_ngen_1601_);
lean_inc(v_nextMacroScope_1600_);
lean_inc(v_env_1599_);
lean_dec(v___x_1598_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1631_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1613_; 
lean_inc(v___x_1584_);
v___x_1610_ = l_Lean_markMeta(v_env_1599_, v___x_1584_);
v___x_1611_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 5, v___x_1611_);
lean_ctor_set(v___x_1608_, 0, v___x_1610_);
v___x_1613_ = v___x_1608_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1610_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_nextMacroScope_1600_);
lean_ctor_set(v_reuseFailAlloc_1630_, 2, v_ngen_1601_);
lean_ctor_set(v_reuseFailAlloc_1630_, 3, v_auxDeclNGen_1602_);
lean_ctor_set(v_reuseFailAlloc_1630_, 4, v_traceState_1603_);
lean_ctor_set(v_reuseFailAlloc_1630_, 5, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1630_, 6, v_messages_1604_);
lean_ctor_set(v_reuseFailAlloc_1630_, 7, v_infoState_1605_);
lean_ctor_set(v_reuseFailAlloc_1630_, 8, v_snapshotTasks_1606_);
v___x_1613_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v_mctx_1616_; lean_object* v_zetaDeltaFVarIds_1617_; lean_object* v_postponed_1618_; lean_object* v_diag_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1628_; 
v___x_1614_ = lean_st_ref_set(v___y_1571_, v___x_1613_);
v___x_1615_ = lean_st_ref_take(v___y_1569_);
v_mctx_1616_ = lean_ctor_get(v___x_1615_, 0);
v_zetaDeltaFVarIds_1617_ = lean_ctor_get(v___x_1615_, 2);
v_postponed_1618_ = lean_ctor_get(v___x_1615_, 3);
v_diag_1619_ = lean_ctor_get(v___x_1615_, 4);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1628_ == 0)
{
lean_object* v_unused_1629_; 
v_unused_1629_ = lean_ctor_get(v___x_1615_, 1);
lean_dec(v_unused_1629_);
v___x_1621_ = v___x_1615_;
v_isShared_1622_ = v_isSharedCheck_1628_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_diag_1619_);
lean_inc(v_postponed_1618_);
lean_inc(v_zetaDeltaFVarIds_1617_);
lean_inc(v_mctx_1616_);
lean_dec(v___x_1615_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1628_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v___x_1625_; 
v___x_1623_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 1, v___x_1623_);
v___x_1625_ = v___x_1621_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_mctx_1616_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v___x_1623_);
lean_ctor_set(v_reuseFailAlloc_1627_, 2, v_zetaDeltaFVarIds_1617_);
lean_ctor_set(v_reuseFailAlloc_1627_, 3, v_postponed_1618_);
lean_ctor_set(v_reuseFailAlloc_1627_, 4, v_diag_1619_);
v___x_1625_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_st_ref_set(v___y_1569_, v___x_1625_);
v___y_1452_ = v___x_1584_;
v___y_1453_ = v___y_1568_;
v___y_1454_ = v___y_1569_;
v___y_1455_ = v___y_1570_;
v___y_1456_ = v___y_1571_;
goto v___jp_1451_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1584_);
lean_dec(v_indName_1445_);
lean_dec(v___x_1443_);
return v___x_1594_;
}
}
}
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec(v_a_1546_);
lean_dec(v_indName_1445_);
lean_dec(v_levelParams_1444_);
lean_dec(v___x_1443_);
lean_dec(v___x_1438_);
v_a_1636_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1574_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1574_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
else
{
lean_dec(v_a_1546_);
lean_dec(v_indName_1445_);
lean_dec(v_levelParams_1444_);
lean_dec(v___x_1443_);
lean_dec(v___x_1438_);
return v___x_1573_;
}
}
else
{
lean_dec(v_a_1546_);
lean_dec(v_indName_1445_);
lean_dec(v_levelParams_1444_);
lean_dec(v___x_1443_);
lean_dec(v___x_1438_);
return v___x_1572_;
}
}
v___jp_1644_:
{
lean_object* v___x_1649_; lean_object* v_env_1650_; uint8_t v___x_1651_; 
v___x_1649_ = lean_st_ref_get(v___y_1648_);
v_env_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc_ref(v_env_1650_);
lean_dec(v___x_1649_);
lean_inc(v_indName_1445_);
v___x_1651_ = l_Lean_isMarkedMeta(v_env_1650_, v_indName_1445_);
if (v___x_1651_ == 0)
{
v___y_1568_ = v___y_1645_;
v___y_1569_ = v___y_1646_;
v___y_1570_ = v___y_1647_;
v___y_1571_ = v___y_1648_;
goto v___jp_1567_;
}
else
{
lean_object* v___x_1652_; lean_object* v_env_1653_; lean_object* v_nextMacroScope_1654_; lean_object* v_ngen_1655_; lean_object* v_auxDeclNGen_1656_; lean_object* v_traceState_1657_; lean_object* v_messages_1658_; lean_object* v_infoState_1659_; lean_object* v_snapshotTasks_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1685_; 
v___x_1652_ = lean_st_ref_take(v___y_1648_);
v_env_1653_ = lean_ctor_get(v___x_1652_, 0);
v_nextMacroScope_1654_ = lean_ctor_get(v___x_1652_, 1);
v_ngen_1655_ = lean_ctor_get(v___x_1652_, 2);
v_auxDeclNGen_1656_ = lean_ctor_get(v___x_1652_, 3);
v_traceState_1657_ = lean_ctor_get(v___x_1652_, 4);
v_messages_1658_ = lean_ctor_get(v___x_1652_, 6);
v_infoState_1659_ = lean_ctor_get(v___x_1652_, 7);
v_snapshotTasks_1660_ = lean_ctor_get(v___x_1652_, 8);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1685_ == 0)
{
lean_object* v_unused_1686_; 
v_unused_1686_ = lean_ctor_get(v___x_1652_, 5);
lean_dec(v_unused_1686_);
v___x_1662_ = v___x_1652_;
v_isShared_1663_ = v_isSharedCheck_1685_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_snapshotTasks_1660_);
lean_inc(v_infoState_1659_);
lean_inc(v_messages_1658_);
lean_inc(v_traceState_1657_);
lean_inc(v_auxDeclNGen_1656_);
lean_inc(v_ngen_1655_);
lean_inc(v_nextMacroScope_1654_);
lean_inc(v_env_1653_);
lean_dec(v___x_1652_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1685_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1667_; 
lean_inc(v___x_1443_);
v___x_1664_ = l_Lean_markMeta(v_env_1653_, v___x_1443_);
v___x_1665_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 5, v___x_1665_);
lean_ctor_set(v___x_1662_, 0, v___x_1664_);
v___x_1667_ = v___x_1662_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1664_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_nextMacroScope_1654_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v_ngen_1655_);
lean_ctor_set(v_reuseFailAlloc_1684_, 3, v_auxDeclNGen_1656_);
lean_ctor_set(v_reuseFailAlloc_1684_, 4, v_traceState_1657_);
lean_ctor_set(v_reuseFailAlloc_1684_, 5, v___x_1665_);
lean_ctor_set(v_reuseFailAlloc_1684_, 6, v_messages_1658_);
lean_ctor_set(v_reuseFailAlloc_1684_, 7, v_infoState_1659_);
lean_ctor_set(v_reuseFailAlloc_1684_, 8, v_snapshotTasks_1660_);
v___x_1667_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v_mctx_1670_; lean_object* v_zetaDeltaFVarIds_1671_; lean_object* v_postponed_1672_; lean_object* v_diag_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1682_; 
v___x_1668_ = lean_st_ref_set(v___y_1648_, v___x_1667_);
v___x_1669_ = lean_st_ref_take(v___y_1646_);
v_mctx_1670_ = lean_ctor_get(v___x_1669_, 0);
v_zetaDeltaFVarIds_1671_ = lean_ctor_get(v___x_1669_, 2);
v_postponed_1672_ = lean_ctor_get(v___x_1669_, 3);
v_diag_1673_ = lean_ctor_get(v___x_1669_, 4);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1682_ == 0)
{
lean_object* v_unused_1683_; 
v_unused_1683_ = lean_ctor_get(v___x_1669_, 1);
lean_dec(v_unused_1683_);
v___x_1675_ = v___x_1669_;
v_isShared_1676_ = v_isSharedCheck_1682_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_diag_1673_);
lean_inc(v_postponed_1672_);
lean_inc(v_zetaDeltaFVarIds_1671_);
lean_inc(v_mctx_1670_);
lean_dec(v___x_1669_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1682_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1677_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 1, v___x_1677_);
v___x_1679_ = v___x_1675_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_mctx_1670_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1681_, 2, v_zetaDeltaFVarIds_1671_);
lean_ctor_set(v_reuseFailAlloc_1681_, 3, v_postponed_1672_);
lean_ctor_set(v_reuseFailAlloc_1681_, 4, v_diag_1673_);
v___x_1679_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_st_ref_set(v___y_1646_, v___x_1679_);
v___y_1568_ = v___y_1645_;
v___y_1569_ = v___y_1646_;
v___y_1570_ = v___y_1647_;
v___y_1571_ = v___y_1648_;
goto v___jp_1567_;
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
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec(v_a_1546_);
lean_dec(v_indName_1445_);
lean_dec(v_levelParams_1444_);
lean_dec(v___x_1443_);
lean_dec(v___x_1438_);
lean_dec_ref(v_val_1436_);
v_a_1763_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1552_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1552_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec(v_indName_1445_);
lean_dec(v_levelParams_1444_);
lean_dec(v___x_1443_);
lean_dec(v___x_1442_);
lean_dec(v_ctors_1441_);
lean_dec_ref(v___x_1440_);
lean_dec(v___x_1439_);
lean_dec(v___x_1438_);
lean_dec_ref(v___x_1437_);
lean_dec_ref(v_val_1436_);
lean_dec_ref(v_xs_1433_);
lean_dec_ref(v___x_1432_);
lean_dec_ref(v___x_1431_);
v_a_1771_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1545_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1545_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec(v_indName_1445_);
lean_dec(v_levelParams_1444_);
lean_dec(v___x_1443_);
lean_dec(v___x_1442_);
lean_dec(v_ctors_1441_);
lean_dec_ref(v___x_1440_);
lean_dec(v___x_1439_);
lean_dec(v___x_1438_);
lean_dec_ref(v___x_1437_);
lean_dec_ref(v_val_1436_);
lean_dec_ref(v_xs_1433_);
lean_dec_ref(v___x_1432_);
lean_dec_ref(v___x_1431_);
v_a_1779_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1542_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1542_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
v___jp_1451_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1457_ = lean_unsigned_to_nat(1u);
v___x_1458_ = lean_mk_empty_array_with_capacity(v___x_1457_);
lean_inc(v___y_1452_);
v___x_1459_ = lean_array_push(v___x_1458_, v___y_1452_);
v___x_1460_ = l_Lean_compileDecls(v___x_1459_, v___x_1435_, v___y_1455_, v___y_1456_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v___x_1461_; lean_object* v_env_1462_; lean_object* v_nextMacroScope_1463_; lean_object* v_ngen_1464_; lean_object* v_auxDeclNGen_1465_; lean_object* v_traceState_1466_; lean_object* v_messages_1467_; lean_object* v_infoState_1468_; lean_object* v_snapshotTasks_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1540_; 
lean_dec_ref(v___x_1460_);
v___x_1461_ = lean_st_ref_take(v___y_1456_);
v_env_1462_ = lean_ctor_get(v___x_1461_, 0);
v_nextMacroScope_1463_ = lean_ctor_get(v___x_1461_, 1);
v_ngen_1464_ = lean_ctor_get(v___x_1461_, 2);
v_auxDeclNGen_1465_ = lean_ctor_get(v___x_1461_, 3);
v_traceState_1466_ = lean_ctor_get(v___x_1461_, 4);
v_messages_1467_ = lean_ctor_get(v___x_1461_, 6);
v_infoState_1468_ = lean_ctor_get(v___x_1461_, 7);
v_snapshotTasks_1469_ = lean_ctor_get(v___x_1461_, 8);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1540_ == 0)
{
lean_object* v_unused_1541_; 
v_unused_1541_ = lean_ctor_get(v___x_1461_, 5);
lean_dec(v_unused_1541_);
v___x_1471_ = v___x_1461_;
v_isShared_1472_ = v_isSharedCheck_1540_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_snapshotTasks_1469_);
lean_inc(v_infoState_1468_);
lean_inc(v_messages_1467_);
lean_inc(v_traceState_1466_);
lean_inc(v_auxDeclNGen_1465_);
lean_inc(v_ngen_1464_);
lean_inc(v_nextMacroScope_1463_);
lean_inc(v_env_1462_);
lean_dec(v___x_1461_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1540_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1476_; 
lean_inc(v___y_1452_);
v___x_1473_ = l_Lean_Meta_addToCompletionBlackList(v_env_1462_, v___y_1452_);
v___x_1474_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 5, v___x_1474_);
lean_ctor_set(v___x_1471_, 0, v___x_1473_);
v___x_1476_ = v___x_1471_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1473_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_nextMacroScope_1463_);
lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_ngen_1464_);
lean_ctor_set(v_reuseFailAlloc_1539_, 3, v_auxDeclNGen_1465_);
lean_ctor_set(v_reuseFailAlloc_1539_, 4, v_traceState_1466_);
lean_ctor_set(v_reuseFailAlloc_1539_, 5, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1539_, 6, v_messages_1467_);
lean_ctor_set(v_reuseFailAlloc_1539_, 7, v_infoState_1468_);
lean_ctor_set(v_reuseFailAlloc_1539_, 8, v_snapshotTasks_1469_);
v___x_1476_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v_mctx_1479_; lean_object* v_zetaDeltaFVarIds_1480_; lean_object* v_postponed_1481_; lean_object* v_diag_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1537_; 
v___x_1477_ = lean_st_ref_set(v___y_1456_, v___x_1476_);
v___x_1478_ = lean_st_ref_take(v___y_1454_);
v_mctx_1479_ = lean_ctor_get(v___x_1478_, 0);
v_zetaDeltaFVarIds_1480_ = lean_ctor_get(v___x_1478_, 2);
v_postponed_1481_ = lean_ctor_get(v___x_1478_, 3);
v_diag_1482_ = lean_ctor_get(v___x_1478_, 4);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; 
v_unused_1538_ = lean_ctor_get(v___x_1478_, 1);
lean_dec(v_unused_1538_);
v___x_1484_ = v___x_1478_;
v_isShared_1485_ = v_isSharedCheck_1537_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_diag_1482_);
lean_inc(v_postponed_1481_);
lean_inc(v_zetaDeltaFVarIds_1480_);
lean_inc(v_mctx_1479_);
lean_dec(v___x_1478_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1537_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1486_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 1, v___x_1486_);
v___x_1488_ = v___x_1484_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_mctx_1479_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1536_, 2, v_zetaDeltaFVarIds_1480_);
lean_ctor_set(v_reuseFailAlloc_1536_, 3, v_postponed_1481_);
lean_ctor_set(v_reuseFailAlloc_1536_, 4, v_diag_1482_);
v___x_1488_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v_env_1491_; lean_object* v_nextMacroScope_1492_; lean_object* v_ngen_1493_; lean_object* v_auxDeclNGen_1494_; lean_object* v_traceState_1495_; lean_object* v_messages_1496_; lean_object* v_infoState_1497_; lean_object* v_snapshotTasks_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1534_; 
v___x_1489_ = lean_st_ref_set(v___y_1454_, v___x_1488_);
v___x_1490_ = lean_st_ref_take(v___y_1456_);
v_env_1491_ = lean_ctor_get(v___x_1490_, 0);
v_nextMacroScope_1492_ = lean_ctor_get(v___x_1490_, 1);
v_ngen_1493_ = lean_ctor_get(v___x_1490_, 2);
v_auxDeclNGen_1494_ = lean_ctor_get(v___x_1490_, 3);
v_traceState_1495_ = lean_ctor_get(v___x_1490_, 4);
v_messages_1496_ = lean_ctor_get(v___x_1490_, 6);
v_infoState_1497_ = lean_ctor_get(v___x_1490_, 7);
v_snapshotTasks_1498_ = lean_ctor_get(v___x_1490_, 8);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1534_ == 0)
{
lean_object* v_unused_1535_; 
v_unused_1535_ = lean_ctor_get(v___x_1490_, 5);
lean_dec(v_unused_1535_);
v___x_1500_ = v___x_1490_;
v_isShared_1501_ = v_isSharedCheck_1534_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_snapshotTasks_1498_);
lean_inc(v_infoState_1497_);
lean_inc(v_messages_1496_);
lean_inc(v_traceState_1495_);
lean_inc(v_auxDeclNGen_1494_);
lean_inc(v_ngen_1493_);
lean_inc(v_nextMacroScope_1492_);
lean_inc(v_env_1491_);
lean_dec(v___x_1490_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1534_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1502_; lean_object* v___x_1504_; 
lean_inc(v___y_1452_);
v___x_1502_ = l_Lean_addProtected(v_env_1491_, v___y_1452_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 5, v___x_1474_);
lean_ctor_set(v___x_1500_, 0, v___x_1502_);
v___x_1504_ = v___x_1500_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_nextMacroScope_1492_);
lean_ctor_set(v_reuseFailAlloc_1533_, 2, v_ngen_1493_);
lean_ctor_set(v_reuseFailAlloc_1533_, 3, v_auxDeclNGen_1494_);
lean_ctor_set(v_reuseFailAlloc_1533_, 4, v_traceState_1495_);
lean_ctor_set(v_reuseFailAlloc_1533_, 5, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1533_, 6, v_messages_1496_);
lean_ctor_set(v_reuseFailAlloc_1533_, 7, v_infoState_1497_);
lean_ctor_set(v_reuseFailAlloc_1533_, 8, v_snapshotTasks_1498_);
v___x_1504_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v_mctx_1507_; lean_object* v_zetaDeltaFVarIds_1508_; lean_object* v_postponed_1509_; lean_object* v_diag_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1531_; 
v___x_1505_ = lean_st_ref_set(v___y_1456_, v___x_1504_);
v___x_1506_ = lean_st_ref_take(v___y_1454_);
v_mctx_1507_ = lean_ctor_get(v___x_1506_, 0);
v_zetaDeltaFVarIds_1508_ = lean_ctor_get(v___x_1506_, 2);
v_postponed_1509_ = lean_ctor_get(v___x_1506_, 3);
v_diag_1510_ = lean_ctor_get(v___x_1506_, 4);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; 
v_unused_1532_ = lean_ctor_get(v___x_1506_, 1);
lean_dec(v_unused_1532_);
v___x_1512_ = v___x_1506_;
v_isShared_1513_ = v_isSharedCheck_1531_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_diag_1510_);
lean_inc(v_postponed_1509_);
lean_inc(v_zetaDeltaFVarIds_1508_);
lean_inc(v_mctx_1507_);
lean_dec(v___x_1506_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1531_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 1, v___x_1486_);
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_mctx_1507_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_zetaDeltaFVarIds_1508_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v_postponed_1509_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v_diag_1510_);
v___x_1515_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1528_; 
v___x_1516_ = lean_st_ref_set(v___y_1454_, v___x_1515_);
lean_inc(v___y_1452_);
v___x_1517_ = l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1517_);
if (v_isSharedCheck_1528_ == 0)
{
lean_object* v_unused_1529_; 
v_unused_1529_ = lean_ctor_get(v___x_1517_, 0);
lean_dec(v_unused_1529_);
v___x_1519_ = v___x_1517_;
v_isShared_1520_ = v_isSharedCheck_1528_;
goto v_resetjp_1518_;
}
else
{
lean_dec(v___x_1517_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1528_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
if (v_isShared_1520_ == 0)
{
lean_ctor_set_tag(v___x_1519_, 1);
lean_ctor_set(v___x_1519_, 0, v___x_1443_);
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1443_);
v___x_1522_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1523_ = lean_box(0);
v___x_1524_ = ((lean_object*)(l_mkCtorIdx___lam__1___closed__1));
v___x_1525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1522_);
lean_ctor_set(v___x_1525_, 1, v___x_1523_);
lean_ctor_set(v___x_1525_, 2, v___x_1524_);
v___x_1526_ = l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(v___y_1452_, v___x_1525_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
return v___x_1526_;
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
lean_dec(v___y_1452_);
lean_dec(v___x_1443_);
return v___x_1460_;
}
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__1___boxed(lean_object** _args){
lean_object* v___x_1787_ = _args[0];
lean_object* v___x_1788_ = _args[1];
lean_object* v_xs_1789_ = _args[2];
lean_object* v___x_1790_ = _args[3];
lean_object* v___x_1791_ = _args[4];
lean_object* v_val_1792_ = _args[5];
lean_object* v___x_1793_ = _args[6];
lean_object* v___x_1794_ = _args[7];
lean_object* v___x_1795_ = _args[8];
lean_object* v___x_1796_ = _args[9];
lean_object* v_ctors_1797_ = _args[10];
lean_object* v___x_1798_ = _args[11];
lean_object* v___x_1799_ = _args[12];
lean_object* v_levelParams_1800_ = _args[13];
lean_object* v_indName_1801_ = _args[14];
lean_object* v___y_1802_ = _args[15];
lean_object* v___y_1803_ = _args[16];
lean_object* v___y_1804_ = _args[17];
lean_object* v___y_1805_ = _args[18];
lean_object* v___y_1806_ = _args[19];
_start:
{
uint8_t v___x_36063__boxed_1807_; uint8_t v___x_36064__boxed_1808_; lean_object* v_res_1809_; 
v___x_36063__boxed_1807_ = lean_unbox(v___x_1790_);
v___x_36064__boxed_1808_ = lean_unbox(v___x_1791_);
v_res_1809_ = l_mkCtorIdx___lam__1(v___x_1787_, v___x_1788_, v_xs_1789_, v___x_36063__boxed_1807_, v___x_36064__boxed_1808_, v_val_1792_, v___x_1793_, v___x_1794_, v___x_1795_, v___x_1796_, v_ctors_1797_, v___x_1798_, v___x_1799_, v_levelParams_1800_, v_indName_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(lean_object* v_bs_1810_, lean_object* v_k_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1810_, v_k_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
v_a_1826_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1817_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1817_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg___boxed(lean_object* v_bs_1834_, lean_object* v_k_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(v_bs_1834_, v_k_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v___y_1837_);
lean_dec_ref(v___y_1836_);
lean_dec_ref(v_bs_1834_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(size_t v_sz_1842_, size_t v_i_1843_, lean_object* v_bs_1844_){
_start:
{
uint8_t v___x_1845_; 
v___x_1845_ = lean_usize_dec_lt(v_i_1843_, v_sz_1842_);
if (v___x_1845_ == 0)
{
return v_bs_1844_;
}
else
{
lean_object* v_v_1846_; lean_object* v___x_1847_; lean_object* v_bs_x27_1848_; lean_object* v___x_1849_; uint8_t v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; size_t v___x_1853_; size_t v___x_1854_; lean_object* v___x_1855_; 
v_v_1846_ = lean_array_uget(v_bs_1844_, v_i_1843_);
v___x_1847_ = lean_unsigned_to_nat(0u);
v_bs_x27_1848_ = lean_array_uset(v_bs_1844_, v_i_1843_, v___x_1847_);
v___x_1849_ = l_Lean_Expr_fvarId_x21(v_v_1846_);
lean_dec(v_v_1846_);
v___x_1850_ = 1;
v___x_1851_ = lean_box(v___x_1850_);
v___x_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1849_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = ((size_t)1ULL);
v___x_1854_ = lean_usize_add(v_i_1843_, v___x_1853_);
v___x_1855_ = lean_array_uset(v_bs_x27_1848_, v_i_1843_, v___x_1852_);
v_i_1843_ = v___x_1854_;
v_bs_1844_ = v___x_1855_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19___boxed(lean_object* v_sz_1857_, lean_object* v_i_1858_, lean_object* v_bs_1859_){
_start:
{
size_t v_sz_boxed_1860_; size_t v_i_boxed_1861_; lean_object* v_res_1862_; 
v_sz_boxed_1860_ = lean_unbox_usize(v_sz_1857_);
lean_dec(v_sz_1857_);
v_i_boxed_1861_ = lean_unbox_usize(v_i_1858_);
lean_dec(v_i_1858_);
v_res_1862_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(v_sz_boxed_1860_, v_i_boxed_1861_, v_bs_1859_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(lean_object* v_bs_1863_, lean_object* v_k_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
size_t v_sz_1870_; size_t v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v_sz_1870_ = lean_array_size(v_bs_1863_);
v___x_1871_ = ((size_t)0ULL);
v___x_1872_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(v_sz_1870_, v___x_1871_, v_bs_1863_);
v___x_1873_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(v___x_1872_, v_k_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
lean_dec_ref(v___x_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg___boxed(lean_object* v_bs_1874_, lean_object* v_k_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(v_bs_1874_, v_k_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__2(lean_object* v_numParams_1885_, lean_object* v_indName_1886_, lean_object* v___x_1887_, lean_object* v___x_1888_, uint8_t v___x_1889_, uint8_t v___x_1890_, lean_object* v_val_1891_, lean_object* v___x_1892_, lean_object* v_ctors_1893_, lean_object* v___x_1894_, lean_object* v_levelParams_1895_, lean_object* v_xs_1896_, lean_object* v_x_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___f_1915_; lean_object* v___x_1916_; 
v___x_1903_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1885_);
lean_inc_ref_n(v_xs_1896_, 3);
v___x_1904_ = l_Array_toSubarray___redArg(v_xs_1896_, v___x_1903_, v_numParams_1885_);
v___x_1905_ = l_Subarray_copy___redArg(v___x_1904_);
v___x_1906_ = lean_array_get_size(v_xs_1896_);
v___x_1907_ = l_Array_toSubarray___redArg(v_xs_1896_, v_numParams_1885_, v___x_1906_);
v___x_1908_ = l_Subarray_copy___redArg(v___x_1907_);
lean_inc(v___x_1887_);
lean_inc(v_indName_1886_);
v___x_1909_ = l_Lean_mkConst(v_indName_1886_, v___x_1887_);
v___x_1910_ = l_Lean_mkAppN(v___x_1909_, v_xs_1896_);
v___x_1911_ = ((lean_object*)(l_mkCtorIdx___lam__2___closed__1));
v___x_1912_ = l_Lean_mkConst(v___x_1911_, v___x_1888_);
v___x_1913_ = lean_box(v___x_1889_);
v___x_1914_ = lean_box(v___x_1890_);
v___f_1915_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__1___boxed), 20, 15);
lean_closure_set(v___f_1915_, 0, v___x_1910_);
lean_closure_set(v___f_1915_, 1, v___x_1912_);
lean_closure_set(v___f_1915_, 2, v_xs_1896_);
lean_closure_set(v___f_1915_, 3, v___x_1913_);
lean_closure_set(v___f_1915_, 4, v___x_1914_);
lean_closure_set(v___f_1915_, 5, v_val_1891_);
lean_closure_set(v___f_1915_, 6, v___x_1908_);
lean_closure_set(v___f_1915_, 7, v___x_1887_);
lean_closure_set(v___f_1915_, 8, v___x_1892_);
lean_closure_set(v___f_1915_, 9, v___x_1905_);
lean_closure_set(v___f_1915_, 10, v_ctors_1893_);
lean_closure_set(v___f_1915_, 11, v___x_1903_);
lean_closure_set(v___f_1915_, 12, v___x_1894_);
lean_closure_set(v___f_1915_, 13, v_levelParams_1895_);
lean_closure_set(v___f_1915_, 14, v_indName_1886_);
v___x_1916_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(v_xs_1896_, v___f_1915_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__2___boxed(lean_object** _args){
lean_object* v_numParams_1917_ = _args[0];
lean_object* v_indName_1918_ = _args[1];
lean_object* v___x_1919_ = _args[2];
lean_object* v___x_1920_ = _args[3];
lean_object* v___x_1921_ = _args[4];
lean_object* v___x_1922_ = _args[5];
lean_object* v_val_1923_ = _args[6];
lean_object* v___x_1924_ = _args[7];
lean_object* v_ctors_1925_ = _args[8];
lean_object* v___x_1926_ = _args[9];
lean_object* v_levelParams_1927_ = _args[10];
lean_object* v_xs_1928_ = _args[11];
lean_object* v_x_1929_ = _args[12];
lean_object* v___y_1930_ = _args[13];
lean_object* v___y_1931_ = _args[14];
lean_object* v___y_1932_ = _args[15];
lean_object* v___y_1933_ = _args[16];
lean_object* v___y_1934_ = _args[17];
_start:
{
uint8_t v___x_36751__boxed_1935_; uint8_t v___x_36752__boxed_1936_; lean_object* v_res_1937_; 
v___x_36751__boxed_1935_ = lean_unbox(v___x_1921_);
v___x_36752__boxed_1936_ = lean_unbox(v___x_1922_);
v_res_1937_ = l_mkCtorIdx___lam__2(v_numParams_1917_, v_indName_1918_, v___x_1919_, v___x_1920_, v___x_36751__boxed_1935_, v___x_36752__boxed_1936_, v_val_1923_, v___x_1924_, v_ctors_1925_, v___x_1926_, v_levelParams_1927_, v_xs_1928_, v_x_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec_ref(v_x_1929_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00mkCtorIdx_spec__3(lean_object* v_a_1938_, lean_object* v_a_1939_){
_start:
{
if (lean_obj_tag(v_a_1938_) == 0)
{
lean_object* v___x_1940_; 
v___x_1940_ = l_List_reverse___redArg(v_a_1939_);
return v___x_1940_;
}
else
{
lean_object* v_head_1941_; lean_object* v_tail_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1951_; 
v_head_1941_ = lean_ctor_get(v_a_1938_, 0);
v_tail_1942_ = lean_ctor_get(v_a_1938_, 1);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_a_1938_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1944_ = v_a_1938_;
v_isShared_1945_ = v_isSharedCheck_1951_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_tail_1942_);
lean_inc(v_head_1941_);
lean_dec(v_a_1938_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1951_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; lean_object* v___x_1948_; 
v___x_1946_ = l_Lean_mkLevelParam(v_head_1941_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 1, v_a_1939_);
lean_ctor_set(v___x_1944_, 0, v___x_1946_);
v___x_1948_ = v___x_1944_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1946_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v_a_1939_);
v___x_1948_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
v_a_1938_ = v_tail_1942_;
v_a_1939_ = v___x_1948_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_mkCtorIdx___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1954_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6));
v___x_1955_ = lean_unsigned_to_nat(62u);
v___x_1956_ = lean_unsigned_to_nat(48u);
v___x_1957_ = ((lean_object*)(l_mkCtorIdx___lam__3___closed__1));
v___x_1958_ = ((lean_object*)(l_mkCtorIdx___lam__3___closed__0));
v___x_1959_ = l_mkPanicMessageWithDecl(v___x_1958_, v___x_1957_, v___x_1956_, v___x_1955_, v___x_1954_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__3(lean_object* v_indName_1960_, uint8_t v___x_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v_options_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
v_options_1967_ = lean_ctor_get(v___y_1964_, 2);
v___x_1968_ = l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx;
v___x_1969_ = l_Lean_Option_get___at___00mkCtorIdx_spec__0(v_options_1967_, v___x_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_dec(v_indName_1960_);
v___x_1970_ = lean_box(0);
v___x_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
return v___x_1971_;
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_2058_; 
lean_inc(v_indName_1960_);
v___x_1972_ = l_mkCtorIdxName(v_indName_1960_);
lean_inc(v___x_1972_);
v___x_1973_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(v___x_1972_, v___x_1969_, v___y_1965_);
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_2058_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_2058_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
uint8_t v___x_1978_; 
v___x_1978_ = lean_unbox(v_a_1974_);
lean_dec(v_a_1974_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; 
lean_del_object(v___x_1976_);
lean_inc(v_indName_1960_);
v___x_1979_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v_indName_1960_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref(v___x_1979_);
if (lean_obj_tag(v_a_1980_) == 5)
{
lean_object* v_val_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2043_; 
v_val_1981_ = lean_ctor_get(v_a_1980_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_a_1980_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_1983_ = v_a_1980_;
v_isShared_1984_ = v_isSharedCheck_2043_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_val_1981_);
lean_dec(v_a_1980_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2043_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v_toConstantVal_1985_; lean_object* v_numParams_1986_; lean_object* v_numIndices_1987_; lean_object* v_ctors_1988_; lean_object* v_levelParams_1989_; lean_object* v_type_1990_; lean_object* v___x_1991_; 
v_toConstantVal_1985_ = lean_ctor_get(v_val_1981_, 0);
v_numParams_1986_ = lean_ctor_get(v_val_1981_, 1);
lean_inc(v_numParams_1986_);
v_numIndices_1987_ = lean_ctor_get(v_val_1981_, 2);
lean_inc(v_numIndices_1987_);
v_ctors_1988_ = lean_ctor_get(v_val_1981_, 4);
lean_inc(v_ctors_1988_);
v_levelParams_1989_ = lean_ctor_get(v_toConstantVal_1985_, 1);
lean_inc(v_levelParams_1989_);
v_type_1990_ = lean_ctor_get(v_toConstantVal_1985_, 2);
lean_inc_ref_n(v_type_1990_, 2);
v___x_1991_ = l_Lean_Meta_isPropFormerType(v_type_1990_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2034_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_1994_ = v___x_1991_;
v_isShared_1995_ = v_isSharedCheck_2034_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2034_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
uint8_t v___x_1996_; 
v___x_1996_ = lean_unbox(v_a_1992_);
lean_dec(v_a_1992_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
lean_del_object(v___x_1994_);
lean_inc(v_indName_1960_);
v___x_1997_ = l_Lean_mkCasesOnName(v_indName_1960_);
lean_inc(v___x_1997_);
v___x_1998_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v___x_1997_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2021_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2001_ = v___x_1998_;
v_isShared_2002_ = v_isSharedCheck_2021_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2021_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; 
v___x_2003_ = l_List_lengthTR___redArg(v_levelParams_1989_);
v___x_2004_ = l_Lean_ConstantInfo_levelParams(v_a_1999_);
lean_dec(v_a_1999_);
v___x_2005_ = l_List_lengthTR___redArg(v___x_2004_);
lean_dec(v___x_2004_);
v___x_2006_ = lean_nat_dec_lt(v___x_2003_, v___x_2005_);
lean_dec(v___x_2005_);
lean_dec(v___x_2003_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; lean_object* v___x_2009_; 
lean_dec(v___x_1997_);
lean_dec_ref(v_type_1990_);
lean_dec(v_levelParams_1989_);
lean_dec(v_ctors_1988_);
lean_dec(v_numIndices_1987_);
lean_dec(v_numParams_1986_);
lean_del_object(v___x_1983_);
lean_dec_ref(v_val_1981_);
lean_dec(v___x_1972_);
lean_dec(v_indName_1960_);
v___x_2007_ = lean_box(0);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2007_);
v___x_2009_ = v___x_2001_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
else
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___f_2015_; lean_object* v___x_2016_; lean_object* v___x_2018_; 
lean_del_object(v___x_2001_);
v___x_2011_ = lean_box(0);
lean_inc(v_levelParams_1989_);
v___x_2012_ = l_List_mapTR_loop___at___00mkCtorIdx_spec__3(v_levelParams_1989_, v___x_2011_);
v___x_2013_ = lean_box(v___x_1961_);
v___x_2014_ = lean_box(v___x_1969_);
lean_inc(v_numParams_1986_);
v___f_2015_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__2___boxed), 18, 11);
lean_closure_set(v___f_2015_, 0, v_numParams_1986_);
lean_closure_set(v___f_2015_, 1, v_indName_1960_);
lean_closure_set(v___f_2015_, 2, v___x_2012_);
lean_closure_set(v___f_2015_, 3, v___x_2011_);
lean_closure_set(v___f_2015_, 4, v___x_2013_);
lean_closure_set(v___f_2015_, 5, v___x_2014_);
lean_closure_set(v___f_2015_, 6, v_val_1981_);
lean_closure_set(v___f_2015_, 7, v___x_1997_);
lean_closure_set(v___f_2015_, 8, v_ctors_1988_);
lean_closure_set(v___f_2015_, 9, v___x_1972_);
lean_closure_set(v___f_2015_, 10, v_levelParams_1989_);
v___x_2016_ = lean_nat_add(v_numParams_1986_, v_numIndices_1987_);
lean_dec(v_numIndices_1987_);
lean_dec(v_numParams_1986_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set_tag(v___x_1983_, 1);
lean_ctor_set(v___x_1983_, 0, v___x_2016_);
v___x_2018_ = v___x_1983_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(v_type_1990_, v___x_2018_, v___f_2015_, v___x_1961_, v___x_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
return v___x_2019_;
}
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec(v___x_1997_);
lean_dec_ref(v_type_1990_);
lean_dec(v_levelParams_1989_);
lean_dec(v_ctors_1988_);
lean_dec(v_numIndices_1987_);
lean_dec(v_numParams_1986_);
lean_del_object(v___x_1983_);
lean_dec_ref(v_val_1981_);
lean_dec(v___x_1972_);
lean_dec(v_indName_1960_);
v_a_2022_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_1998_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_1998_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2032_; 
lean_dec_ref(v_type_1990_);
lean_dec(v_levelParams_1989_);
lean_dec(v_ctors_1988_);
lean_dec(v_numIndices_1987_);
lean_dec(v_numParams_1986_);
lean_del_object(v___x_1983_);
lean_dec_ref(v_val_1981_);
lean_dec(v___x_1972_);
lean_dec(v_indName_1960_);
v___x_2030_ = lean_box(0);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v___x_2030_);
v___x_2032_ = v___x_1994_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec_ref(v_type_1990_);
lean_dec(v_levelParams_1989_);
lean_dec(v_ctors_1988_);
lean_dec(v_numIndices_1987_);
lean_dec(v_numParams_1986_);
lean_del_object(v___x_1983_);
lean_dec_ref(v_val_1981_);
lean_dec(v___x_1972_);
lean_dec(v_indName_1960_);
v_a_2035_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_1991_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_1991_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
lean_dec(v_a_1980_);
lean_dec(v___x_1972_);
lean_dec(v_indName_1960_);
v___x_2044_ = lean_obj_once(&l_mkCtorIdx___lam__3___closed__2, &l_mkCtorIdx___lam__3___closed__2_once, _init_l_mkCtorIdx___lam__3___closed__2);
v___x_2045_ = l_panic___at___00mkCtorIdx_spec__13(v___x_2044_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
return v___x_2045_;
}
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
lean_dec(v___x_1972_);
lean_dec(v_indName_1960_);
v_a_2046_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_1979_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_1979_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2056_; 
lean_dec(v___x_1972_);
lean_dec(v_indName_1960_);
v___x_2054_ = lean_box(0);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_2054_);
v___x_2056_ = v___x_1976_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__3___boxed(lean_object* v_indName_2059_, lean_object* v___x_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
uint8_t v___x_36864__boxed_2066_; lean_object* v_res_2067_; 
v___x_36864__boxed_2066_ = lean_unbox(v___x_2060_);
v_res_2067_ = l_mkCtorIdx___lam__3(v_indName_2059_, v___x_36864__boxed_2066_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__4(lean_object* v___x_2068_, lean_object* v_e_2069_){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = l_Lean_indentD(v_e_2069_);
v___x_2071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2068_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__5(lean_object* v___f_2072_, lean_object* v___f_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v___x_2079_; 
v___x_2079_ = l_Lean_Meta_mapErrorImp___redArg(v___f_2072_, v___f_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2079_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2079_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
v_a_2088_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2079_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2079_);
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
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__5___boxed(lean_object* v___f_2096_, lean_object* v___f_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_mkCtorIdx___lam__5(v___f_2096_, v___f_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
return v_res_2103_;
}
}
static lean_object* _init_l_mkCtorIdx___closed__1(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = ((lean_object*)(l_mkCtorIdx___closed__0));
v___x_2106_ = l_Lean_stringToMessageData(v___x_2105_);
return v___x_2106_;
}
}
static lean_object* _init_l_mkCtorIdx___closed__3(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = ((lean_object*)(l_mkCtorIdx___closed__2));
v___x_2109_ = l_Lean_stringToMessageData(v___x_2108_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx(lean_object* v_indName_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_){
_start:
{
lean_object* v___x_2116_; uint8_t v___x_2117_; lean_object* v___x_2118_; lean_object* v___f_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___f_2124_; lean_object* v___f_2125_; uint8_t v___x_2126_; 
v___x_2116_ = lean_obj_once(&l_mkCtorIdx___closed__1, &l_mkCtorIdx___closed__1_once, _init_l_mkCtorIdx___closed__1);
v___x_2117_ = 0;
v___x_2118_ = lean_box(v___x_2117_);
lean_inc_n(v_indName_2110_, 2);
v___f_2119_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__3___boxed), 7, 2);
lean_closure_set(v___f_2119_, 0, v_indName_2110_);
lean_closure_set(v___f_2119_, 1, v___x_2118_);
v___x_2120_ = l_Lean_MessageData_ofConstName(v_indName_2110_, v___x_2117_);
v___x_2121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2116_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = lean_obj_once(&l_mkCtorIdx___closed__3, &l_mkCtorIdx___closed__3_once, _init_l_mkCtorIdx___closed__3);
v___x_2123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2121_);
lean_ctor_set(v___x_2123_, 1, v___x_2122_);
v___f_2124_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__4), 2, 1);
lean_closure_set(v___f_2124_, 0, v___x_2123_);
v___f_2125_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__5___boxed), 7, 2);
lean_closure_set(v___f_2125_, 0, v___f_2119_);
lean_closure_set(v___f_2125_, 1, v___f_2124_);
v___x_2126_ = l_Lean_isPrivateName(v_indName_2110_);
lean_dec(v_indName_2110_);
if (v___x_2126_ == 0)
{
uint8_t v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = 1;
v___x_2128_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(v___f_2125_, v___x_2127_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
return v___x_2128_;
}
else
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(v___f_2125_, v___x_2117_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
return v___x_2129_;
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___boxed(lean_object* v_indName_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_mkCtorIdx(v_indName_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6(uint8_t v___x_2137_, lean_object* v___x_2138_, lean_object* v_as_2139_, lean_object* v_as_x27_2140_, lean_object* v_b_2141_, lean_object* v_a_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(v___x_2137_, v___x_2138_, v_as_x27_2140_, v_b_2141_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___boxed(lean_object* v___x_2149_, lean_object* v___x_2150_, lean_object* v_as_2151_, lean_object* v_as_x27_2152_, lean_object* v_b_2153_, lean_object* v_a_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
uint8_t v___x_37171__boxed_2160_; lean_object* v_res_2161_; 
v___x_37171__boxed_2160_ = lean_unbox(v___x_2149_);
v_res_2161_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6(v___x_37171__boxed_2160_, v___x_2150_, v_as_2151_, v_as_x27_2152_, v_b_2153_, v_a_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v_as_2151_);
lean_dec_ref(v___x_2150_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10(lean_object* v_00_u03b1_2162_, lean_object* v_name_2163_, uint8_t v_bi_2164_, lean_object* v_type_2165_, lean_object* v_k_2166_, uint8_t v_kind_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v___x_2173_; 
v___x_2173_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(v_name_2163_, v_bi_2164_, v_type_2165_, v_k_2166_, v_kind_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2174_, lean_object* v_name_2175_, lean_object* v_bi_2176_, lean_object* v_type_2177_, lean_object* v_k_2178_, lean_object* v_kind_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
uint8_t v_bi_boxed_2185_; uint8_t v_kind_boxed_2186_; lean_object* v_res_2187_; 
v_bi_boxed_2185_ = lean_unbox(v_bi_2176_);
v_kind_boxed_2186_ = lean_unbox(v_kind_2179_);
v_res_2187_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10(v_00_u03b1_2174_, v_name_2175_, v_bi_boxed_2185_, v_type_2177_, v_k_2178_, v_kind_boxed_2186_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7(lean_object* v_00_u03b1_2188_, lean_object* v_name_2189_, lean_object* v_type_2190_, lean_object* v_k_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(v_name_2189_, v_type_2190_, v_k_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___boxed(lean_object* v_00_u03b1_2198_, lean_object* v_name_2199_, lean_object* v_type_2200_, lean_object* v_k_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7(v_00_u03b1_2198_, v_name_2199_, v_type_2200_, v_k_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15(lean_object* v_declName_2208_, uint8_t v_s_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(v_declName_2208_, v_s_2209_, v___y_2211_, v___y_2213_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___boxed(lean_object* v_declName_2216_, lean_object* v_s_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
uint8_t v_s_boxed_2223_; lean_object* v_res_2224_; 
v_s_boxed_2223_ = lean_unbox(v_s_2217_);
v_res_2224_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15(v_declName_2216_, v_s_boxed_2223_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17(lean_object* v_env_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v___x_2231_; 
v___x_2231_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(v_env_2225_, v___y_2227_, v___y_2229_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___boxed(lean_object* v_env_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17(v_env_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20(lean_object* v_00_u03b1_2239_, lean_object* v_bs_2240_, lean_object* v_k_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(v_bs_2240_, v_k_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___boxed(lean_object* v_00_u03b1_2248_, lean_object* v_bs_2249_, lean_object* v_k_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20(v_00_u03b1_2248_, v_bs_2249_, v_k_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec_ref(v_bs_2249_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12(lean_object* v_00_u03b1_2257_, lean_object* v_bs_2258_, lean_object* v_k_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(v_bs_2258_, v_k_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___boxed(lean_object* v_00_u03b1_2266_, lean_object* v_bs_2267_, lean_object* v_k_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12(v_00_u03b1_2266_, v_bs_2267_, v_k_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2(lean_object* v_00_u03b1_2275_, lean_object* v_constName_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(v_constName_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2283_, lean_object* v_constName_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2(v_00_u03b1_2283_, v_constName_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5(lean_object* v_00_u03b1_2291_, lean_object* v_msg_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v_msg_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2299_, lean_object* v_msg_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5(v_00_u03b1_2299_, v_msg_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7(lean_object* v_00_u03b1_2307_, lean_object* v_ref_2308_, lean_object* v_constName_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_2308_, v_constName_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___boxed(lean_object* v_00_u03b1_2316_, lean_object* v_ref_2317_, lean_object* v_constName_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7(v_00_u03b1_2316_, v_ref_2317_, v_constName_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v_ref_2317_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21(lean_object* v_00_u03b1_2325_, lean_object* v_ref_2326_, lean_object* v_msg_2327_, lean_object* v_declHint_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_2326_, v_msg_2327_, v_declHint_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___boxed(lean_object* v_00_u03b1_2335_, lean_object* v_ref_2336_, lean_object* v_msg_2337_, lean_object* v_declHint_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21(v_00_u03b1_2335_, v_ref_2336_, v_msg_2337_, v_declHint_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v_ref_2336_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(lean_object* v_msg_2345_, lean_object* v_declHint_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_2345_, v_declHint_2346_, v___y_2350_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___boxed(lean_object* v_msg_2353_, lean_object* v_declHint_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(v_msg_2353_, v_declHint_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(lean_object* v_00_u03b1_2361_, lean_object* v_ref_2362_, lean_object* v_msg_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_2362_, v_msg_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___boxed(lean_object* v_00_u03b1_2370_, lean_object* v_ref_2371_, lean_object* v_msg_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(v_00_u03b1_2370_, v_ref_2371_, v_msg_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v_ref_2371_);
return v_res_2378_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Deprecated(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = l___private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx);
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
