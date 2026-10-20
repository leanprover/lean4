// Lean compiler output
// Module: Lean.Meta.Constructions.SparseCasesOn
// Imports: public import Lean.Meta.Basic import Lean.AddDecl import Lean.Meta.Constructions.CtorIdx import Lean.Meta.HasNotBit import Lean.Meta.Transform
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
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
lean_object* l_Lean_mkHasNotBitProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_uint64_to_usize(uint64_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasExposedBody(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkHasNotBit(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_ConstantInfo_value_x21(lean_object*, uint8_t);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited___redArg();
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_markSparseCasesOn(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_mkCtorIdxName(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey___closed__0_value;
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0 = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Constructions"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(224, 107, 212, 234, 74, 49, 105, 87)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "SparseCasesOn"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 142, 211, 52, 27, 176, 89, 6)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(93, 38, 184, 128, 76, 32, 215, 209)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(232, 79, 91, 86, 222, 171, 161, 209)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(36, 83, 47, 52, 170, 238, 223, 102)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "sparseCasesOnCacheExt"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(106, 173, 73, 104, 127, 128, 171, 122)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt;
static const lean_array_object l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__0_value)}};
static const lean_object* l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1 = (const lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedSparseCasesOnInfo_default = (const lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedSparseCasesOnInfo = (const lean_object*)&l_Lean_Meta_instInhabitedSparseCasesOnInfo_default___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "sparseCasesOnInfoExt"};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 231, 162, 79, 58, 254, 239, 178)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11_spec__27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Meta.Constructions.SparseCasesOn"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.mkSparseCasesOn"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "sparse `casesOn` for `"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` is already registered as `"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__0___closed__3_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16_spec__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16_spec__24___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__9(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__2 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__2_value;
static const lean_ctor_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 140, 41, 106, 106, 114, 66, 206)}};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3_value;
static const lean_array_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "mkSparseCasesOn: unexpected number of parameters in type of `"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5_value;
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__18;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__18___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "mkSparseCasesOn: constructor "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = " is not a constructor of "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkSparseCasesOn_spec__7(lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___closed__0;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "mkSparseCasesOn: unexpected number of universe parameters in `"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__1 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__1_value;
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___closed__2;
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___closed__3;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "_sparseCasesOn"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__4 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__4_value;
static const lean_ctor_object l_Lean_Meta_mkSparseCasesOn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__4_value),LEAN_SCALAR_PTR_LITERAL(111, 99, 43, 146, 60, 255, 155, 135)}};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__5 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__5_value;
static const lean_string_object l_Lean_Meta_mkSparseCasesOn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "mkSparseCasesOn: requested casesOn combinator is not sparse"};
static const lean_object* l_Lean_Meta_mkSparseCasesOn___closed__6 = (const lean_object*)&l_Lean_Meta_mkSparseCasesOn___closed__6_value;
static lean_once_cell_t l_Lean_Meta_mkSparseCasesOn___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkSparseCasesOn___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfoCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(lean_object* v_xs_1_, lean_object* v_ys_2_, lean_object* v_x_3_){
_start:
{
lean_object* v_zero_4_; uint8_t v_isZero_5_; 
v_zero_4_ = lean_unsigned_to_nat(0u);
v_isZero_5_ = lean_nat_dec_eq(v_x_3_, v_zero_4_);
if (v_isZero_5_ == 1)
{
lean_dec(v_x_3_);
return v_isZero_5_;
}
else
{
lean_object* v_one_6_; lean_object* v_n_7_; lean_object* v___x_8_; lean_object* v___x_9_; uint8_t v___x_10_; 
v_one_6_ = lean_unsigned_to_nat(1u);
v_n_7_ = lean_nat_sub(v_x_3_, v_one_6_);
lean_dec(v_x_3_);
v___x_8_ = lean_array_fget_borrowed(v_xs_1_, v_n_7_);
v___x_9_ = lean_array_fget_borrowed(v_ys_2_, v_n_7_);
v___x_10_ = lean_name_eq(v___x_8_, v___x_9_);
if (v___x_10_ == 0)
{
lean_dec(v_n_7_);
return v___x_10_;
}
else
{
v_x_3_ = v_n_7_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg___boxed(lean_object* v_xs_12_, lean_object* v_ys_13_, lean_object* v_x_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(v_xs_12_, v_ys_13_, v_x_14_);
lean_dec_ref(v_ys_13_);
lean_dec_ref(v_xs_12_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
lean_object* v_indName_19_; lean_object* v_ctors_20_; uint8_t v_isPrivate_21_; lean_object* v_indName_22_; lean_object* v_ctors_23_; uint8_t v_isPrivate_24_; uint8_t v___x_25_; 
v_indName_19_ = lean_ctor_get(v_x_17_, 0);
v_ctors_20_ = lean_ctor_get(v_x_17_, 1);
v_isPrivate_21_ = lean_ctor_get_uint8(v_x_17_, sizeof(void*)*2);
v_indName_22_ = lean_ctor_get(v_x_18_, 0);
v_ctors_23_ = lean_ctor_get(v_x_18_, 1);
v_isPrivate_24_ = lean_ctor_get_uint8(v_x_18_, sizeof(void*)*2);
v___x_25_ = lean_name_eq(v_indName_19_, v_indName_22_);
if (v___x_25_ == 0)
{
return v___x_25_;
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_26_ = lean_array_get_size(v_ctors_20_);
v___x_27_ = lean_array_get_size(v_ctors_23_);
v___x_28_ = lean_nat_dec_eq(v___x_26_, v___x_27_);
if (v___x_28_ == 0)
{
return v___x_28_;
}
else
{
uint8_t v___x_29_; 
v___x_29_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(v_ctors_20_, v_ctors_23_, v___x_26_);
if (v___x_29_ == 0)
{
return v___x_29_;
}
else
{
if (v_isPrivate_24_ == 0)
{
if (v_isPrivate_21_ == 0)
{
return v___x_29_;
}
else
{
return v_isPrivate_24_;
}
}
else
{
return v_isPrivate_21_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq___boxed(lean_object* v_x_30_, lean_object* v_x_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_30_, v_x_31_);
lean_dec_ref(v_x_31_);
lean_dec_ref(v_x_30_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0(lean_object* v_xs_34_, lean_object* v_ys_35_, lean_object* v_hsz_36_, lean_object* v_x_37_, lean_object* v_x_38_){
_start:
{
uint8_t v___x_39_; 
v___x_39_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___redArg(v_xs_34_, v_ys_35_, v_x_37_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0___boxed(lean_object* v_xs_40_, lean_object* v_ys_41_, lean_object* v_hsz_42_, lean_object* v_x_43_, lean_object* v_x_44_){
_start:
{
uint8_t v_res_45_; lean_object* v_r_46_; 
v_res_45_ = l_Array_isEqvAux___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq_spec__0(v_xs_40_, v_ys_41_, v_hsz_42_, v_x_43_, v_x_44_);
lean_dec_ref(v_ys_41_);
lean_dec_ref(v_xs_40_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(lean_object* v_as_49_, size_t v_i_50_, size_t v_stop_51_, uint64_t v_b_52_){
_start:
{
uint64_t v___y_54_; uint8_t v___x_59_; 
v___x_59_ = lean_usize_dec_eq(v_i_50_, v_stop_51_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; 
v___x_60_ = lean_array_uget_borrowed(v_as_49_, v_i_50_);
if (lean_obj_tag(v___x_60_) == 0)
{
uint64_t v___x_61_; 
v___x_61_ = 1723ULL;
v___y_54_ = v___x_61_;
goto v___jp_53_;
}
else
{
uint64_t v_hash_62_; 
v_hash_62_ = lean_ctor_get_uint64(v___x_60_, sizeof(void*)*2);
v___y_54_ = v_hash_62_;
goto v___jp_53_;
}
}
else
{
return v_b_52_;
}
v___jp_53_:
{
uint64_t v___x_55_; size_t v___x_56_; size_t v___x_57_; 
v___x_55_ = lean_uint64_mix_hash(v_b_52_, v___y_54_);
v___x_56_ = ((size_t)1ULL);
v___x_57_ = lean_usize_add(v_i_50_, v___x_56_);
v_i_50_ = v___x_57_;
v_b_52_ = v___x_55_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0___boxed(lean_object* v_as_63_, lean_object* v_i_64_, lean_object* v_stop_65_, lean_object* v_b_66_){
_start:
{
size_t v_i_boxed_67_; size_t v_stop_boxed_68_; uint64_t v_b_boxed_69_; uint64_t v_res_70_; lean_object* v_r_71_; 
v_i_boxed_67_ = lean_unbox_usize(v_i_64_);
lean_dec(v_i_64_);
v_stop_boxed_68_ = lean_unbox_usize(v_stop_65_);
lean_dec(v_stop_65_);
v_b_boxed_69_ = lean_unbox_uint64(v_b_66_);
lean_dec_ref(v_b_66_);
v_res_70_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(v_as_63_, v_i_boxed_67_, v_stop_boxed_68_, v_b_boxed_69_);
lean_dec_ref(v_as_63_);
v_r_71_ = lean_box_uint64(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(lean_object* v_x_72_){
_start:
{
lean_object* v_indName_73_; lean_object* v_ctors_74_; uint8_t v_isPrivate_75_; uint64_t v___y_77_; uint64_t v___y_78_; uint64_t v___x_84_; uint64_t v___y_86_; 
v_indName_73_ = lean_ctor_get(v_x_72_, 0);
v_ctors_74_ = lean_ctor_get(v_x_72_, 1);
v_isPrivate_75_ = lean_ctor_get_uint8(v_x_72_, sizeof(void*)*2);
v___x_84_ = 0ULL;
if (lean_obj_tag(v_indName_73_) == 0)
{
uint64_t v___x_95_; 
v___x_95_ = 1723ULL;
v___y_86_ = v___x_95_;
goto v___jp_85_;
}
else
{
uint64_t v_hash_96_; 
v_hash_96_ = lean_ctor_get_uint64(v_indName_73_, sizeof(void*)*2);
v___y_86_ = v_hash_96_;
goto v___jp_85_;
}
v___jp_76_:
{
uint64_t v___x_79_; 
v___x_79_ = lean_uint64_mix_hash(v___y_77_, v___y_78_);
if (v_isPrivate_75_ == 0)
{
uint64_t v___x_80_; uint64_t v___x_81_; 
v___x_80_ = 13ULL;
v___x_81_ = lean_uint64_mix_hash(v___x_79_, v___x_80_);
return v___x_81_;
}
else
{
uint64_t v___x_82_; uint64_t v___x_83_; 
v___x_82_ = 11ULL;
v___x_83_ = lean_uint64_mix_hash(v___x_79_, v___x_82_);
return v___x_83_;
}
}
v___jp_85_:
{
uint64_t v___x_87_; uint64_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_87_ = lean_uint64_mix_hash(v___x_84_, v___y_86_);
v___x_88_ = 7ULL;
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = lean_array_get_size(v_ctors_74_);
v___x_91_ = lean_nat_dec_lt(v___x_89_, v___x_90_);
if (v___x_91_ == 0)
{
v___y_77_ = v___x_87_;
v___y_78_ = v___x_88_;
goto v___jp_76_;
}
else
{
size_t v___x_92_; size_t v___x_93_; uint64_t v___x_94_; 
v___x_92_ = ((size_t)0ULL);
v___x_93_ = lean_usize_of_nat(v___x_90_);
v___x_94_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash_spec__0(v_ctors_74_, v___x_92_, v___x_93_, v___x_88_);
v___y_77_ = v___x_87_;
v___y_78_ = v___x_94_;
goto v___jp_76_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash___boxed(lean_object* v_x_97_){
_start:
{
uint64_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_x_97_);
lean_dec_ref(v_x_97_);
v_r_99_ = lean_box_uint64(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(lean_object* v___x_102_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_102_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2____boxed(lean_object* v___x_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(v___x_105_);
return v_res_107_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_111_; lean_object* v___f_112_; 
v___x_111_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_);
v___f_112_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_112_, 0, v___x_111_);
return v___f_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; uint8_t v___x_152_; lean_object* v___x_153_; 
v___f_147_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_);
v___x_148_ = lean_box(0);
v___x_149_ = lean_box(1);
v___x_150_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_));
v___x_151_ = 0;
v___x_152_ = 1;
v___x_153_ = l_Lean_registerEnvExtension___redArg(v___f_147_, v___x_148_, v___x_149_, v___x_150_, v___x_151_, v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2____boxed(lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_();
return v_res_155_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(lean_object* v_env_164_, lean_object* v_n_165_, lean_object* v_x_166_){
_start:
{
uint8_t v___x_167_; 
v___x_167_ = l_Lean_Environment_hasExposedBody(v_env_164_, v_n_165_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2____boxed(lean_object* v_env_168_, lean_object* v_n_169_, lean_object* v_x_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(v_env_168_, v_n_169_, v_x_170_);
lean_dec_ref(v_x_170_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_173_, lean_object* v_x_174_){
_start:
{
if (lean_obj_tag(v_x_174_) == 0)
{
lean_object* v_k_175_; lean_object* v_v_176_; lean_object* v_l_177_; lean_object* v_r_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v_k_175_ = lean_ctor_get(v_x_174_, 1);
v_v_176_ = lean_ctor_get(v_x_174_, 2);
v_l_177_ = lean_ctor_get(v_x_174_, 3);
v_r_178_ = lean_ctor_get(v_x_174_, 4);
v___x_179_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(v_init_173_, v_l_177_);
lean_inc(v_v_176_);
lean_inc(v_k_175_);
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v_k_175_);
lean_ctor_set(v___x_180_, 1, v_v_176_);
v___x_181_ = lean_array_push(v___x_179_, v___x_180_);
v_init_173_ = v___x_181_;
v_x_174_ = v_r_178_;
goto _start;
}
else
{
return v_init_173_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_183_, lean_object* v_x_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(v_init_183_, v_x_184_);
lean_dec(v_x_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(lean_object* v_env_188_, lean_object* v_s_189_){
_start:
{
lean_object* v___f_190_; lean_object* v___x_191_; lean_object* v_all_192_; lean_object* v___x_193_; lean_object* v_exported_194_; lean_object* v___x_195_; 
v___f_190_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(v___f_190_, 0, v_env_188_);
v___x_191_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_));
v_all_192_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(v___x_191_, v_s_189_);
v___x_193_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v___f_190_, v_s_189_);
v_exported_194_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(v___x_191_, v___x_193_);
lean_dec(v___x_193_);
lean_inc_ref(v_exported_194_);
v___x_195_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_195_, 0, v_exported_194_);
lean_ctor_set(v___x_195_, 1, v_exported_194_);
lean_ctor_set(v___x_195_, 2, v_all_192_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_204_; lean_object* v___x_205_; lean_object* v___x_206_; uint8_t v___x_207_; lean_object* v___x_208_; 
v___f_204_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_));
v___x_205_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_));
v___x_206_ = ((lean_object*)(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_));
v___x_207_ = 0;
v___x_208_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_205_, v___x_206_, v___x_207_, v___f_204_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2____boxed(lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_();
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0(lean_object* v_init_211_, lean_object* v_t_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0_spec__0(v_init_211_, v_t_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_214_, lean_object* v_t_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2__spec__0(v_init_214_, v_t_215_);
lean_dec(v_t_215_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(lean_object* v_kind_217_, lean_object* v___y_218_){
_start:
{
lean_object* v___x_220_; lean_object* v_auxDeclNGen_221_; lean_object* v___x_222_; lean_object* v_env_223_; lean_object* v___x_224_; lean_object* v_fst_225_; lean_object* v_snd_226_; lean_object* v___x_227_; lean_object* v_env_228_; lean_object* v_nextMacroScope_229_; lean_object* v_ngen_230_; lean_object* v_traceState_231_; lean_object* v_cache_232_; lean_object* v_recordedDeps_233_; lean_object* v_messages_234_; lean_object* v_infoState_235_; lean_object* v_snapshotTasks_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_245_; 
v___x_220_ = lean_st_ref_get(v___y_218_);
v_auxDeclNGen_221_ = lean_ctor_get(v___x_220_, 3);
lean_inc_ref(v_auxDeclNGen_221_);
lean_dec(v___x_220_);
v___x_222_ = lean_st_ref_get(v___y_218_);
v_env_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc_ref(v_env_223_);
lean_dec(v___x_222_);
v___x_224_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_223_, v_auxDeclNGen_221_, v_kind_217_);
v_fst_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_fst_225_);
v_snd_226_ = lean_ctor_get(v___x_224_, 1);
lean_inc(v_snd_226_);
lean_dec_ref(v___x_224_);
v___x_227_ = lean_st_ref_take(v___y_218_);
v_env_228_ = lean_ctor_get(v___x_227_, 0);
v_nextMacroScope_229_ = lean_ctor_get(v___x_227_, 1);
v_ngen_230_ = lean_ctor_get(v___x_227_, 2);
v_traceState_231_ = lean_ctor_get(v___x_227_, 4);
v_cache_232_ = lean_ctor_get(v___x_227_, 5);
v_recordedDeps_233_ = lean_ctor_get(v___x_227_, 6);
v_messages_234_ = lean_ctor_get(v___x_227_, 7);
v_infoState_235_ = lean_ctor_get(v___x_227_, 8);
v_snapshotTasks_236_ = lean_ctor_get(v___x_227_, 9);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; 
v_unused_246_ = lean_ctor_get(v___x_227_, 3);
lean_dec(v_unused_246_);
v___x_238_ = v___x_227_;
v_isShared_239_ = v_isSharedCheck_245_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_snapshotTasks_236_);
lean_inc(v_infoState_235_);
lean_inc(v_messages_234_);
lean_inc(v_recordedDeps_233_);
lean_inc(v_cache_232_);
lean_inc(v_traceState_231_);
lean_inc(v_ngen_230_);
lean_inc(v_nextMacroScope_229_);
lean_inc(v_env_228_);
lean_dec(v___x_227_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_245_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 3, v_snd_226_);
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_env_228_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_nextMacroScope_229_);
lean_ctor_set(v_reuseFailAlloc_244_, 2, v_ngen_230_);
lean_ctor_set(v_reuseFailAlloc_244_, 3, v_snd_226_);
lean_ctor_set(v_reuseFailAlloc_244_, 4, v_traceState_231_);
lean_ctor_set(v_reuseFailAlloc_244_, 5, v_cache_232_);
lean_ctor_set(v_reuseFailAlloc_244_, 6, v_recordedDeps_233_);
lean_ctor_set(v_reuseFailAlloc_244_, 7, v_messages_234_);
lean_ctor_set(v_reuseFailAlloc_244_, 8, v_infoState_235_);
lean_ctor_set(v_reuseFailAlloc_244_, 9, v_snapshotTasks_236_);
v___x_241_ = v_reuseFailAlloc_244_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_st_ref_put(v___y_218_, v___x_241_);
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v_fst_225_);
return v___x_243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg___boxed(lean_object* v_kind_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(v_kind_247_, v___y_248_);
lean_dec(v___y_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2(lean_object* v_kind_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(v_kind_251_, v___y_255_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___boxed(lean_object* v_kind_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2(v_kind_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__4(lean_object* v_s_265_, lean_object* v_msg_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = lean_panic_fn_borrowed(v_s_265_, v_msg_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__4___boxed(lean_object* v_s_268_, lean_object* v_msg_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__4(v_s_268_, v_msg_269_);
lean_dec_ref(v_s_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___lam__0(lean_object* v_k_271_, lean_object* v_b_272_, lean_object* v_c_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v___x_279_; 
lean_inc(v___y_277_);
lean_inc_ref(v___y_276_);
lean_inc(v___y_275_);
lean_inc_ref(v___y_274_);
v___x_279_ = lean_apply_7(v_k_271_, v_b_272_, v_c_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, lean_box(0));
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___lam__0___boxed(lean_object* v_k_280_, lean_object* v_b_281_, lean_object* v_c_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___lam__0(v_k_280_, v_b_281_, v_c_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg(lean_object* v_type_289_, lean_object* v_k_290_, uint8_t v_cleanupAnnotations_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___f_297_; uint8_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___f_297_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_297_, 0, v_k_290_);
v___x_298_ = 0;
v___x_299_ = lean_box(0);
v___x_300_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_298_, v___x_299_, v_type_289_, v___f_297_, v_cleanupAnnotations_291_, v___x_298_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
v_a_309_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_300_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_300_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg___boxed(lean_object* v_type_317_, lean_object* v_k_318_, lean_object* v_cleanupAnnotations_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_325_; lean_object* v_res_326_; 
v_cleanupAnnotations_boxed_325_ = lean_unbox(v_cleanupAnnotations_319_);
v_res_326_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg(v_type_317_, v_k_318_, v_cleanupAnnotations_boxed_325_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12(lean_object* v_00_u03b1_327_, lean_object* v_type_328_, lean_object* v_k_329_, uint8_t v_cleanupAnnotations_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg(v_type_328_, v_k_329_, v_cleanupAnnotations_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___boxed(lean_object* v_00_u03b1_337_, lean_object* v_type_338_, lean_object* v_k_339_, lean_object* v_cleanupAnnotations_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_346_; lean_object* v_res_347_; 
v_cleanupAnnotations_boxed_346_ = lean_unbox(v_cleanupAnnotations_340_);
v_res_347_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12(v_00_u03b1_337_, v_type_338_, v_k_339_, v_cleanupAnnotations_boxed_346_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg(lean_object* v_name_348_, lean_object* v_levelParams_349_, lean_object* v_type_350_, lean_object* v_value_351_, lean_object* v_hints_352_, lean_object* v___y_353_){
_start:
{
lean_object* v___x_355_; uint8_t v___y_357_; lean_object* v_env_365_; uint8_t v___x_366_; 
v___x_355_ = lean_st_ref_get(v___y_353_);
v_env_365_ = lean_ctor_get(v___x_355_, 0);
lean_inc_ref_n(v_env_365_, 2);
lean_dec(v___x_355_);
v___x_366_ = l_Lean_Environment_hasUnsafe(v_env_365_, v_type_350_);
if (v___x_366_ == 0)
{
uint8_t v___x_367_; 
v___x_367_ = l_Lean_Environment_hasUnsafe(v_env_365_, v_value_351_);
if (v___x_367_ == 0)
{
uint8_t v___x_368_; 
v___x_368_ = 1;
v___y_357_ = v___x_368_;
goto v___jp_356_;
}
else
{
goto v___jp_363_;
}
}
else
{
lean_dec_ref(v_env_365_);
goto v___jp_363_;
}
v___jp_356_:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
lean_inc(v_name_348_);
v___x_358_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_358_, 0, v_name_348_);
lean_ctor_set(v___x_358_, 1, v_levelParams_349_);
lean_ctor_set(v___x_358_, 2, v_type_350_);
v___x_359_ = lean_box(0);
v___x_360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_360_, 0, v_name_348_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_361_, 0, v___x_358_);
lean_ctor_set(v___x_361_, 1, v_value_351_);
lean_ctor_set(v___x_361_, 2, v_hints_352_);
lean_ctor_set(v___x_361_, 3, v___x_360_);
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*4, v___y_357_);
v___x_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
return v___x_362_;
}
v___jp_363_:
{
uint8_t v___x_364_; 
v___x_364_ = 0;
v___y_357_ = v___x_364_;
goto v___jp_356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg___boxed(lean_object* v_name_369_, lean_object* v_levelParams_370_, lean_object* v_type_371_, lean_object* v_value_372_, lean_object* v_hints_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg(v_name_369_, v_levelParams_370_, v_type_371_, v_value_372_, v_hints_373_, v___y_374_);
lean_dec(v___y_374_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15(lean_object* v_name_377_, lean_object* v_levelParams_378_, lean_object* v_type_379_, lean_object* v_value_380_, lean_object* v_hints_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg(v_name_377_, v_levelParams_378_, v_type_379_, v_value_380_, v_hints_381_, v___y_385_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___boxed(lean_object* v_name_388_, lean_object* v_levelParams_389_, lean_object* v_type_390_, lean_object* v_value_391_, lean_object* v_hints_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15(v_name_388_, v_levelParams_389_, v_type_390_, v_value_391_, v_hints_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17(lean_object* v_msg_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v___f_406_; lean_object* v___x_17660__overap_407_; lean_object* v___x_408_; 
v___f_406_ = ((lean_object*)(l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17___closed__0));
v___x_17660__overap_407_ = lean_panic_fn_borrowed(v___f_406_, v_msg_400_);
lean_inc(v___y_404_);
lean_inc_ref(v___y_403_);
lean_inc(v___y_402_);
lean_inc_ref(v___y_401_);
v___x_408_ = lean_apply_5(v___x_17660__overap_407_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, lean_box(0));
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17___boxed(lean_object* v_msg_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17(v_msg_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11_spec__27___redArg(lean_object* v_x_416_, lean_object* v_x_417_, lean_object* v_x_418_, lean_object* v_x_419_){
_start:
{
lean_object* v_ks_420_; lean_object* v_vs_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_445_; 
v_ks_420_ = lean_ctor_get(v_x_416_, 0);
v_vs_421_ = lean_ctor_get(v_x_416_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v_x_416_);
if (v_isSharedCheck_445_ == 0)
{
v___x_423_ = v_x_416_;
v_isShared_424_ = v_isSharedCheck_445_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_vs_421_);
lean_inc(v_ks_420_);
lean_dec(v_x_416_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_445_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_425_ = lean_array_get_size(v_ks_420_);
v___x_426_ = lean_nat_dec_lt(v_x_417_, v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
lean_dec(v_x_417_);
v___x_427_ = lean_array_push(v_ks_420_, v_x_418_);
v___x_428_ = lean_array_push(v_vs_421_, v_x_419_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v___x_428_);
lean_ctor_set(v___x_423_, 0, v___x_427_);
v___x_430_ = v___x_423_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
else
{
lean_object* v_k_x27_432_; uint8_t v___x_433_; 
v_k_x27_432_ = lean_array_fget_borrowed(v_ks_420_, v_x_417_);
v___x_433_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_418_, v_k_x27_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_435_; 
if (v_isShared_424_ == 0)
{
v___x_435_ = v___x_423_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_ks_420_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_vs_421_);
v___x_435_ = v_reuseFailAlloc_439_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = lean_unsigned_to_nat(1u);
v___x_437_ = lean_nat_add(v_x_417_, v___x_436_);
lean_dec(v_x_417_);
v_x_416_ = v___x_435_;
v_x_417_ = v___x_437_;
goto _start;
}
}
else
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_440_ = lean_array_fset(v_ks_420_, v_x_417_, v_x_418_);
v___x_441_ = lean_array_fset(v_vs_421_, v_x_417_, v_x_419_);
lean_dec(v_x_417_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v___x_441_);
lean_ctor_set(v___x_423_, 0, v___x_440_);
v___x_443_ = v___x_423_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(lean_object* v_n_446_, lean_object* v_k_447_, lean_object* v_v_448_){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11_spec__27___redArg(v_n_446_, v___x_449_, v_k_447_, v_v_448_);
return v___x_450_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(lean_object* v_x_452_, size_t v_x_453_, size_t v_x_454_, lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
if (lean_obj_tag(v_x_452_) == 0)
{
lean_object* v_es_457_; size_t v___x_458_; size_t v___x_459_; lean_object* v_j_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v_es_457_ = lean_ctor_get(v_x_452_, 0);
v___x_458_ = ((size_t)31ULL);
v___x_459_ = lean_usize_land(v_x_453_, v___x_458_);
v_j_460_ = lean_usize_to_nat(v___x_459_);
v___x_461_ = lean_array_get_size(v_es_457_);
v___x_462_ = lean_nat_dec_lt(v_j_460_, v___x_461_);
if (v___x_462_ == 0)
{
lean_dec(v_j_460_);
lean_dec(v_x_456_);
lean_dec_ref(v_x_455_);
return v_x_452_;
}
else
{
lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_501_; 
lean_inc_ref(v_es_457_);
v_isSharedCheck_501_ = !lean_is_exclusive(v_x_452_);
if (v_isSharedCheck_501_ == 0)
{
lean_object* v_unused_502_; 
v_unused_502_ = lean_ctor_get(v_x_452_, 0);
lean_dec(v_unused_502_);
v___x_464_ = v_x_452_;
v_isShared_465_ = v_isSharedCheck_501_;
goto v_resetjp_463_;
}
else
{
lean_dec(v_x_452_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_501_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v_v_466_; lean_object* v___x_467_; lean_object* v_xs_x27_468_; lean_object* v___y_470_; 
v_v_466_ = lean_array_fget(v_es_457_, v_j_460_);
v___x_467_ = lean_box(0);
v_xs_x27_468_ = lean_array_fset(v_es_457_, v_j_460_, v___x_467_);
switch(lean_obj_tag(v_v_466_))
{
case 0:
{
lean_object* v_key_475_; lean_object* v_val_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_486_; 
v_key_475_ = lean_ctor_get(v_v_466_, 0);
v_val_476_ = lean_ctor_get(v_v_466_, 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v_v_466_);
if (v_isSharedCheck_486_ == 0)
{
v___x_478_ = v_v_466_;
v_isShared_479_ = v_isSharedCheck_486_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_val_476_);
lean_inc(v_key_475_);
lean_dec(v_v_466_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_486_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
uint8_t v___x_480_; 
v___x_480_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_455_, v_key_475_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; 
lean_del_object(v___x_478_);
v___x_481_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_475_, v_val_476_, v_x_455_, v_x_456_);
v___x_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
v___y_470_ = v___x_482_;
goto v___jp_469_;
}
else
{
lean_object* v___x_484_; 
lean_dec(v_val_476_);
lean_dec(v_key_475_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v_x_456_);
lean_ctor_set(v___x_478_, 0, v_x_455_);
v___x_484_ = v___x_478_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_x_455_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_x_456_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
v___y_470_ = v___x_484_;
goto v___jp_469_;
}
}
}
}
case 1:
{
lean_object* v_node_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_499_; 
v_node_487_ = lean_ctor_get(v_v_466_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v_v_466_);
if (v_isSharedCheck_499_ == 0)
{
v___x_489_ = v_v_466_;
v_isShared_490_ = v_isSharedCheck_499_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_node_487_);
lean_dec(v_v_466_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_499_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
size_t v___x_491_; size_t v___x_492_; size_t v___x_493_; size_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_491_ = ((size_t)5ULL);
v___x_492_ = lean_usize_shift_right(v_x_453_, v___x_491_);
v___x_493_ = ((size_t)1ULL);
v___x_494_ = lean_usize_add(v_x_454_, v___x_493_);
v___x_495_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_node_487_, v___x_492_, v___x_494_, v_x_455_, v_x_456_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_495_);
v___x_497_ = v___x_489_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
v___y_470_ = v___x_497_;
goto v___jp_469_;
}
}
}
default: 
{
lean_object* v___x_500_; 
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v_x_455_);
lean_ctor_set(v___x_500_, 1, v_x_456_);
v___y_470_ = v___x_500_;
goto v___jp_469_;
}
}
v___jp_469_:
{
lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_471_ = lean_array_fset(v_xs_x27_468_, v_j_460_, v___y_470_);
lean_dec(v_j_460_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_471_);
v___x_473_ = v___x_464_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
else
{
lean_object* v_ks_503_; lean_object* v_vs_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_522_; 
v_ks_503_ = lean_ctor_get(v_x_452_, 0);
v_vs_504_ = lean_ctor_get(v_x_452_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_x_452_);
if (v_isSharedCheck_522_ == 0)
{
v___x_506_ = v_x_452_;
v_isShared_507_ = v_isSharedCheck_522_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_vs_504_);
lean_inc(v_ks_503_);
lean_dec(v_x_452_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_522_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_ks_503_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_vs_504_);
v___x_509_ = v_reuseFailAlloc_521_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v_newNode_510_; size_t v___x_511_; uint8_t v___x_512_; 
v_newNode_510_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(v___x_509_, v_x_455_, v_x_456_);
v___x_511_ = ((size_t)7ULL);
v___x_512_ = lean_usize_dec_le(v___x_511_, v_x_454_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_513_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_510_);
v___x_514_ = lean_unsigned_to_nat(4u);
v___x_515_ = lean_nat_dec_lt(v___x_513_, v___x_514_);
lean_dec(v___x_513_);
if (v___x_515_ == 0)
{
lean_object* v_ks_516_; lean_object* v_vs_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_ks_516_ = lean_ctor_get(v_newNode_510_, 0);
lean_inc_ref(v_ks_516_);
v_vs_517_ = lean_ctor_get(v_newNode_510_, 1);
lean_inc_ref(v_vs_517_);
lean_dec_ref(v_newNode_510_);
v___x_518_ = lean_unsigned_to_nat(0u);
v___x_519_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___closed__0);
v___x_520_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg(v_x_454_, v_ks_516_, v_vs_517_, v___x_518_, v___x_519_);
lean_dec_ref(v_vs_517_);
lean_dec_ref(v_ks_516_);
return v___x_520_;
}
else
{
return v_newNode_510_;
}
}
else
{
return v_newNode_510_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg(size_t v_depth_523_, lean_object* v_keys_524_, lean_object* v_vals_525_, lean_object* v_i_526_, lean_object* v_entries_527_){
_start:
{
lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_528_ = lean_array_get_size(v_keys_524_);
v___x_529_ = lean_nat_dec_lt(v_i_526_, v___x_528_);
if (v___x_529_ == 0)
{
lean_dec(v_i_526_);
return v_entries_527_;
}
else
{
lean_object* v_k_530_; lean_object* v_v_531_; uint64_t v___x_532_; size_t v_h_533_; size_t v___x_534_; lean_object* v___x_535_; size_t v___x_536_; size_t v___x_537_; size_t v___x_538_; size_t v_h_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_k_530_ = lean_array_fget_borrowed(v_keys_524_, v_i_526_);
v_v_531_ = lean_array_fget_borrowed(v_vals_525_, v_i_526_);
v___x_532_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_k_530_);
v_h_533_ = lean_uint64_to_usize(v___x_532_);
v___x_534_ = ((size_t)5ULL);
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = ((size_t)1ULL);
v___x_537_ = lean_usize_sub(v_depth_523_, v___x_536_);
v___x_538_ = lean_usize_mul(v___x_534_, v___x_537_);
v_h_539_ = lean_usize_shift_right(v_h_533_, v___x_538_);
v___x_540_ = lean_nat_add(v_i_526_, v___x_535_);
lean_dec(v_i_526_);
lean_inc(v_v_531_);
lean_inc(v_k_530_);
v___x_541_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_entries_527_, v_h_539_, v_depth_523_, v_k_530_, v_v_531_);
v_i_526_ = v___x_540_;
v_entries_527_ = v___x_541_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg___boxed(lean_object* v_depth_543_, lean_object* v_keys_544_, lean_object* v_vals_545_, lean_object* v_i_546_, lean_object* v_entries_547_){
_start:
{
size_t v_depth_boxed_548_; lean_object* v_res_549_; 
v_depth_boxed_548_ = lean_unbox_usize(v_depth_543_);
lean_dec(v_depth_543_);
v_res_549_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg(v_depth_boxed_548_, v_keys_544_, v_vals_545_, v_i_546_, v_entries_547_);
lean_dec_ref(v_vals_545_);
lean_dec_ref(v_keys_544_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg___boxed(lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
size_t v_x_21790__boxed_555_; size_t v_x_21791__boxed_556_; lean_object* v_res_557_; 
v_x_21790__boxed_555_ = lean_unbox_usize(v_x_551_);
lean_dec(v_x_551_);
v_x_21791__boxed_556_ = lean_unbox_usize(v_x_552_);
lean_dec(v_x_552_);
v_res_557_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_550_, v_x_21790__boxed_555_, v_x_21791__boxed_556_, v_x_553_, v_x_554_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(lean_object* v_x_558_, lean_object* v_x_559_, lean_object* v_x_560_){
_start:
{
uint64_t v___x_561_; size_t v___x_562_; size_t v___x_563_; lean_object* v___x_564_; 
v___x_561_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_x_559_);
v___x_562_ = lean_uint64_to_usize(v___x_561_);
v___x_563_ = ((size_t)1ULL);
v___x_564_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_558_, v___x_562_, v___x_563_, v_x_559_, v_x_560_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___redArg(lean_object* v_keys_565_, lean_object* v_vals_566_, lean_object* v_i_567_, lean_object* v_k_568_){
_start:
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = lean_array_get_size(v_keys_565_);
v___x_570_ = lean_nat_dec_lt(v_i_567_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; 
lean_dec(v_i_567_);
v___x_571_ = lean_box(0);
return v___x_571_;
}
else
{
lean_object* v_k_x27_572_; uint8_t v___x_573_; 
v_k_x27_572_ = lean_array_fget_borrowed(v_keys_565_, v_i_567_);
v___x_573_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_k_568_, v_k_x27_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_unsigned_to_nat(1u);
v___x_575_ = lean_nat_add(v_i_567_, v___x_574_);
lean_dec(v_i_567_);
v_i_567_ = v___x_575_;
goto _start;
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_array_fget_borrowed(v_vals_566_, v_i_567_);
lean_dec(v_i_567_);
lean_inc(v___x_577_);
v___x_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___redArg___boxed(lean_object* v_keys_579_, lean_object* v_vals_580_, lean_object* v_i_581_, lean_object* v_k_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___redArg(v_keys_579_, v_vals_580_, v_i_581_, v_k_582_);
lean_dec_ref(v_k_582_);
lean_dec_ref(v_vals_580_);
lean_dec_ref(v_keys_579_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(lean_object* v_x_584_, size_t v_x_585_, lean_object* v_x_586_){
_start:
{
if (lean_obj_tag(v_x_584_) == 0)
{
lean_object* v_es_587_; lean_object* v___x_588_; size_t v___x_589_; size_t v___x_590_; lean_object* v_j_591_; lean_object* v___x_592_; 
v_es_587_ = lean_ctor_get(v_x_584_, 0);
v___x_588_ = lean_box(2);
v___x_589_ = ((size_t)31ULL);
v___x_590_ = lean_usize_land(v_x_585_, v___x_589_);
v_j_591_ = lean_usize_to_nat(v___x_590_);
v___x_592_ = lean_array_get_borrowed(v___x_588_, v_es_587_, v_j_591_);
lean_dec(v_j_591_);
switch(lean_obj_tag(v___x_592_))
{
case 0:
{
lean_object* v_key_593_; lean_object* v_val_594_; uint8_t v___x_595_; 
v_key_593_ = lean_ctor_get(v___x_592_, 0);
v_val_594_ = lean_ctor_get(v___x_592_, 1);
v___x_595_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instBEqSparseCasesOnKey_beq(v_x_586_, v_key_593_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; 
v___x_596_ = lean_box(0);
return v___x_596_;
}
else
{
lean_object* v___x_597_; 
lean_inc(v_val_594_);
v___x_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_597_, 0, v_val_594_);
return v___x_597_;
}
}
case 1:
{
lean_object* v_node_598_; size_t v___x_599_; size_t v___x_600_; 
v_node_598_ = lean_ctor_get(v___x_592_, 0);
v___x_599_ = ((size_t)5ULL);
v___x_600_ = lean_usize_shift_right(v_x_585_, v___x_599_);
v_x_584_ = v_node_598_;
v_x_585_ = v___x_600_;
goto _start;
}
default: 
{
lean_object* v___x_602_; 
v___x_602_ = lean_box(0);
return v___x_602_;
}
}
}
else
{
lean_object* v_ks_603_; lean_object* v_vs_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_ks_603_ = lean_ctor_get(v_x_584_, 0);
v_vs_604_ = lean_ctor_get(v_x_584_, 1);
v___x_605_ = lean_unsigned_to_nat(0u);
v___x_606_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___redArg(v_ks_603_, v_vs_604_, v___x_605_, v_x_586_);
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg___boxed(lean_object* v_x_607_, lean_object* v_x_608_, lean_object* v_x_609_){
_start:
{
size_t v_x_21974__boxed_610_; lean_object* v_res_611_; 
v_x_21974__boxed_610_ = lean_unbox_usize(v_x_608_);
lean_dec(v_x_608_);
v_res_611_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_607_, v_x_21974__boxed_610_, v_x_609_);
lean_dec_ref(v_x_609_);
lean_dec_ref(v_x_607_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(lean_object* v_x_612_, lean_object* v_x_613_){
_start:
{
uint64_t v___x_614_; size_t v___x_615_; lean_object* v___x_616_; 
v___x_614_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_instHashableSparseCasesOnKey_hash(v_x_613_);
v___x_615_ = lean_uint64_to_usize(v___x_614_);
v___x_616_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_612_, v___x_615_, v_x_613_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg___boxed(lean_object* v_x_617_, lean_object* v_x_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v_x_617_, v_x_618_);
lean_dec_ref(v_x_618_);
lean_dec_ref(v_x_617_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__0(lean_object* v___x_625_, lean_object* v_a_626_, lean_object* v_s_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v_s_627_, v___x_625_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(v_s_627_, v___x_625_, v_a_626_);
return v___x_629_;
}
else
{
lean_object* v_val_630_; uint8_t v___x_631_; 
lean_dec_ref(v___x_625_);
v_val_630_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_val_630_);
lean_dec_ref_known(v___x_628_, 1);
v___x_631_ = lean_name_eq(v_val_630_, v_a_626_);
if (v___x_631_ == 0)
{
uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_632_ = 1;
v___x_633_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__0));
v___x_634_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__1));
v___x_635_ = lean_unsigned_to_nat(144u);
v___x_636_ = lean_unsigned_to_nat(8u);
v___x_637_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__2));
v___x_638_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_626_, v___x_632_);
v___x_639_ = lean_string_append(v___x_637_, v___x_638_);
lean_dec_ref(v___x_638_);
v___x_640_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__3));
v___x_641_ = lean_string_append(v___x_639_, v___x_640_);
v___x_642_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_630_, v___x_632_);
v___x_643_ = lean_string_append(v___x_641_, v___x_642_);
lean_dec_ref(v___x_642_);
v___x_644_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__4));
v___x_645_ = lean_string_append(v___x_643_, v___x_644_);
v___x_646_ = l_mkPanicMessageWithDecl(v___x_633_, v___x_634_, v___x_635_, v___x_636_, v___x_645_);
lean_dec_ref(v___x_645_);
v___x_647_ = lean_panic_fn_borrowed(v_s_627_, v___x_646_);
lean_dec_ref(v_s_627_);
return v___x_647_;
}
else
{
lean_dec(v_val_630_);
lean_dec(v_a_626_);
return v_s_627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__1(lean_object* v___x_648_, lean_object* v___x_649_, lean_object* v___x_650_, uint8_t v___x_651_, lean_object* v_h_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; uint8_t v___x_661_; lean_object* v___x_662_; 
v___x_658_ = lean_array_push(v___x_648_, v_h_652_);
v___x_659_ = l_Lean_mkAppN(v___x_649_, v___x_650_);
v___x_660_ = 1;
v___x_661_ = 1;
v___x_662_ = l_Lean_Meta_mkForallFVars(v___x_658_, v___x_659_, v___x_651_, v___x_660_, v___x_660_, v___x_661_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
lean_dec_ref(v___x_658_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__1___boxed(lean_object* v___x_663_, lean_object* v___x_664_, lean_object* v___x_665_, lean_object* v___x_666_, lean_object* v_h_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
uint8_t v___x_22095__boxed_673_; lean_object* v_res_674_; 
v___x_22095__boxed_673_ = lean_unbox(v___x_666_);
v_res_674_ = l_Lean_Meta_mkSparseCasesOn___lam__1(v___x_663_, v___x_664_, v___x_665_, v___x_22095__boxed_673_, v_h_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec_ref(v___x_665_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14_spec__20(lean_object* v_msgData_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v___x_681_; lean_object* v_env_682_; uint8_t v___x_683_; lean_object* v_env_684_; lean_object* v___x_685_; lean_object* v_toCold_686_; lean_object* v_mctx_687_; lean_object* v_lctx_688_; lean_object* v_options_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_681_ = lean_st_ref_get(v___y_679_);
v_env_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc_ref(v_env_682_);
lean_dec(v___x_681_);
v___x_683_ = 0;
v_env_684_ = l_Lean_Environment_setRecordingDeps(v_env_682_, v___x_683_);
v___x_685_ = lean_st_ref_get(v___y_677_);
v_toCold_686_ = lean_ctor_get(v___y_678_, 0);
v_mctx_687_ = lean_ctor_get(v___x_685_, 0);
lean_inc_ref(v_mctx_687_);
lean_dec(v___x_685_);
v_lctx_688_ = lean_ctor_get(v___y_676_, 2);
v_options_689_ = lean_ctor_get(v_toCold_686_, 2);
lean_inc_ref(v_options_689_);
lean_inc_ref(v_lctx_688_);
v___x_690_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_690_, 0, v_env_684_);
lean_ctor_set(v___x_690_, 1, v_mctx_687_);
lean_ctor_set(v___x_690_, 2, v_lctx_688_);
lean_ctor_set(v___x_690_, 3, v_options_689_);
v___x_691_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v_msgData_675_);
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14_spec__20___boxed(lean_object* v_msgData_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14_spec__20(v_msgData_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(lean_object* v_msg_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v_ref_706_; lean_object* v___x_707_; lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_716_; 
v_ref_706_ = lean_ctor_get(v___y_703_, 2);
v___x_707_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14_spec__20(v_msg_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
v_a_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_716_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_716_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_716_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
lean_inc(v_ref_706_);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v_ref_706_);
lean_ctor_set(v___x_712_, 1, v_a_708_);
if (v_isShared_711_ == 0)
{
lean_ctor_set_tag(v___x_710_, 1);
lean_ctor_set(v___x_710_, 0, v___x_712_);
v___x_714_ = v___x_710_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg___boxed(lean_object* v_msg_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v_msg_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
return v_res_723_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_instMonadEIO___redArg();
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(lean_object* v_msg_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v_toApplicative_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_798_; 
v___x_735_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__0);
v___x_736_ = l_StateRefT_x27_instMonad___redArg(v___x_735_);
v_toApplicative_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; 
v_unused_799_ = lean_ctor_get(v___x_736_, 1);
lean_dec(v_unused_799_);
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_798_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_toApplicative_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_798_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v_toFunctor_741_; lean_object* v_toSeq_742_; lean_object* v_toSeqLeft_743_; lean_object* v_toSeqRight_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_796_; 
v_toFunctor_741_ = lean_ctor_get(v_toApplicative_737_, 0);
v_toSeq_742_ = lean_ctor_get(v_toApplicative_737_, 2);
v_toSeqLeft_743_ = lean_ctor_get(v_toApplicative_737_, 3);
v_toSeqRight_744_ = lean_ctor_get(v_toApplicative_737_, 4);
v_isSharedCheck_796_ = !lean_is_exclusive(v_toApplicative_737_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; 
v_unused_797_ = lean_ctor_get(v_toApplicative_737_, 1);
lean_dec(v_unused_797_);
v___x_746_ = v_toApplicative_737_;
v_isShared_747_ = v_isSharedCheck_796_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_toSeqRight_744_);
lean_inc(v_toSeqLeft_743_);
lean_inc(v_toSeq_742_);
lean_inc(v_toFunctor_741_);
lean_dec(v_toApplicative_737_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_796_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___f_748_; lean_object* v___f_749_; lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___x_752_; lean_object* v___f_753_; lean_object* v___f_754_; lean_object* v___f_755_; lean_object* v___x_757_; 
v___f_748_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__1));
v___f_749_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_741_);
v___f_750_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_750_, 0, v_toFunctor_741_);
v___f_751_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_751_, 0, v_toFunctor_741_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v___f_750_);
lean_ctor_set(v___x_752_, 1, v___f_751_);
v___f_753_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_753_, 0, v_toSeqRight_744_);
v___f_754_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_754_, 0, v_toSeqLeft_743_);
v___f_755_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_755_, 0, v_toSeq_742_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 4, v___f_753_);
lean_ctor_set(v___x_746_, 3, v___f_754_);
lean_ctor_set(v___x_746_, 2, v___f_755_);
lean_ctor_set(v___x_746_, 1, v___f_748_);
lean_ctor_set(v___x_746_, 0, v___x_752_);
v___x_757_ = v___x_746_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___f_748_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v___f_755_);
lean_ctor_set(v_reuseFailAlloc_795_, 3, v___f_754_);
lean_ctor_set(v_reuseFailAlloc_795_, 4, v___f_753_);
v___x_757_ = v_reuseFailAlloc_795_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_759_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v___f_749_);
lean_ctor_set(v___x_739_, 0, v___x_757_);
v___x_759_ = v___x_739_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v___f_749_);
v___x_759_ = v_reuseFailAlloc_794_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; lean_object* v_toApplicative_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_792_; 
v___x_760_ = l_StateRefT_x27_instMonad___redArg(v___x_759_);
v_toApplicative_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v___x_760_, 1);
lean_dec(v_unused_793_);
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_792_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_toApplicative_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_792_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v_toFunctor_765_; lean_object* v_toSeq_766_; lean_object* v_toSeqLeft_767_; lean_object* v_toSeqRight_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_790_; 
v_toFunctor_765_ = lean_ctor_get(v_toApplicative_761_, 0);
v_toSeq_766_ = lean_ctor_get(v_toApplicative_761_, 2);
v_toSeqLeft_767_ = lean_ctor_get(v_toApplicative_761_, 3);
v_toSeqRight_768_ = lean_ctor_get(v_toApplicative_761_, 4);
v_isSharedCheck_790_ = !lean_is_exclusive(v_toApplicative_761_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; 
v_unused_791_ = lean_ctor_get(v_toApplicative_761_, 1);
lean_dec(v_unused_791_);
v___x_770_ = v_toApplicative_761_;
v_isShared_771_ = v_isSharedCheck_790_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_toSeqRight_768_);
lean_inc(v_toSeqLeft_767_);
lean_inc(v_toSeq_766_);
lean_inc(v_toFunctor_765_);
lean_dec(v_toApplicative_761_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_790_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___f_772_; lean_object* v___f_773_; lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___x_776_; lean_object* v___f_777_; lean_object* v___f_778_; lean_object* v___f_779_; lean_object* v___x_781_; 
v___f_772_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__3));
v___f_773_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___closed__4));
lean_inc_ref(v_toFunctor_765_);
v___f_774_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_774_, 0, v_toFunctor_765_);
v___f_775_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_775_, 0, v_toFunctor_765_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___f_774_);
lean_ctor_set(v___x_776_, 1, v___f_775_);
v___f_777_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_777_, 0, v_toSeqRight_768_);
v___f_778_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_778_, 0, v_toSeqLeft_767_);
v___f_779_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_779_, 0, v_toSeq_766_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 4, v___f_777_);
lean_ctor_set(v___x_770_, 3, v___f_778_);
lean_ctor_set(v___x_770_, 2, v___f_779_);
lean_ctor_set(v___x_770_, 1, v___f_772_);
lean_ctor_set(v___x_770_, 0, v___x_776_);
v___x_781_ = v___x_770_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v___f_772_);
lean_ctor_set(v_reuseFailAlloc_789_, 2, v___f_779_);
lean_ctor_set(v_reuseFailAlloc_789_, 3, v___f_778_);
lean_ctor_set(v_reuseFailAlloc_789_, 4, v___f_777_);
v___x_781_ = v_reuseFailAlloc_789_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_783_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 1, v___f_773_);
lean_ctor_set(v___x_763_, 0, v___x_781_);
v___x_783_ = v___x_763_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v___f_773_);
v___x_783_ = v_reuseFailAlloc_788_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_17939__overap_786_; lean_object* v___x_787_; 
v___x_784_ = lean_box(0);
v___x_785_ = l_instInhabitedOfMonad___redArg(v___x_783_, v___x_784_);
v___x_17939__overap_786_ = lean_panic_fn_borrowed(v___x_785_, v_msg_729_);
lean_dec(v___x_785_);
lean_inc(v___y_733_);
lean_inc_ref(v___y_732_);
lean_inc(v___y_731_);
lean_inc_ref(v___y_730_);
v___x_787_ = lean_apply_5(v___x_17939__overap_786_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, lean_box(0));
return v___x_787_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(v_msg_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
return v_res_806_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__4));
v___x_808_ = l_Lean_stringToMessageData(v___x_807_);
return v___x_808_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2(void){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__1));
v___x_811_ = l_Lean_stringToMessageData(v___x_810_);
return v___x_811_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_815_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5));
v___x_816_ = lean_unsigned_to_nat(11u);
v___x_817_ = lean_unsigned_to_nat(122u);
v___x_818_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__4));
v___x_819_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__3));
v___x_820_ = l_mkPanicMessageWithDecl(v___x_819_, v___x_818_, v___x_817_, v___x_816_, v___x_815_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(lean_object* v_constName_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_835_; lean_object* v_env_836_; uint8_t v___x_837_; lean_object* v___x_838_; 
v___x_835_ = lean_st_ref_get(v___y_825_);
v_env_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc_ref(v_env_836_);
lean_dec(v___x_835_);
v___x_837_ = 0;
lean_inc(v_constName_821_);
v___x_838_ = l_Lean_Environment_findAsync_x3f(v_env_836_, v_constName_821_, v___x_837_);
if (lean_obj_tag(v___x_838_) == 1)
{
lean_object* v_val_839_; uint8_t v_kind_840_; 
v_val_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_val_839_);
lean_dec_ref_known(v___x_838_, 1);
v_kind_840_ = lean_ctor_get_uint8(v_val_839_, sizeof(void*)*3);
if (v_kind_840_ == 6)
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_839_);
if (lean_obj_tag(v___x_841_) == 6)
{
lean_object* v_val_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec(v_constName_821_);
v_val_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_val_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set_tag(v___x_844_, 0);
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_val_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec_ref(v___x_841_);
v___x_850_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__6);
v___x_851_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0_spec__0(v___x_850_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_860_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_860_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
if (lean_obj_tag(v_a_852_) == 0)
{
lean_del_object(v___x_854_);
goto v___jp_827_;
}
else
{
lean_object* v_val_856_; lean_object* v___x_858_; 
lean_dec(v_constName_821_);
v_val_856_ = lean_ctor_get(v_a_852_, 0);
lean_inc(v_val_856_);
lean_dec_ref_known(v_a_852_, 1);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v_val_856_);
v___x_858_ = v___x_854_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_val_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_dec(v_constName_821_);
v_a_861_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_851_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_851_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
else
{
lean_dec(v_val_839_);
goto v___jp_827_;
}
}
else
{
lean_dec(v___x_838_);
goto v___jp_827_;
}
v___jp_827_:
{
lean_object* v___x_828_; uint8_t v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_828_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0);
v___x_829_ = 0;
v___x_830_ = l_Lean_MessageData_ofConstName(v_constName_821_, v___x_829_);
v___x_831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_828_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__2);
v___x_833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_831_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___x_833_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
return v___x_834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___boxed(lean_object* v_constName_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_constName_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16_spec__24(lean_object* v_xs_876_, lean_object* v_v_877_, lean_object* v_i_878_){
_start:
{
lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_879_ = lean_array_get_size(v_xs_876_);
v___x_880_ = lean_nat_dec_lt(v_i_878_, v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; 
lean_dec(v_i_878_);
v___x_881_ = lean_box(0);
return v___x_881_;
}
else
{
lean_object* v___x_882_; uint8_t v___x_883_; 
v___x_882_ = lean_array_fget_borrowed(v_xs_876_, v_i_878_);
v___x_883_ = lean_name_eq(v___x_882_, v_v_877_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = lean_unsigned_to_nat(1u);
v___x_885_ = lean_nat_add(v_i_878_, v___x_884_);
lean_dec(v_i_878_);
v_i_878_ = v___x_885_;
goto _start;
}
else
{
lean_object* v___x_887_; 
v___x_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_887_, 0, v_i_878_);
return v___x_887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16_spec__24___boxed(lean_object* v_xs_888_, lean_object* v_v_889_, lean_object* v_i_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16_spec__24(v_xs_888_, v_v_889_, v_i_890_);
lean_dec(v_v_889_);
lean_dec_ref(v_xs_888_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16(lean_object* v_xs_892_, lean_object* v_v_893_){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16_spec__24(v_xs_892_, v_v_893_, v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16___boxed(lean_object* v_xs_896_, lean_object* v_v_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16(v_xs_896_, v_v_897_);
lean_dec(v_v_897_);
lean_dec_ref(v_xs_896_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11(lean_object* v_xs_899_, lean_object* v_v_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11_spec__16(v_xs_899_, v_v_900_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v___x_902_; 
v___x_902_ = lean_box(0);
return v___x_902_;
}
else
{
lean_object* v_val_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
v_val_903_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_901_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_val_903_);
lean_dec(v___x_901_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_val_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11___boxed(lean_object* v_xs_911_, lean_object* v_v_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11(v_xs_911_, v_v_912_);
lean_dec(v_v_912_);
lean_dec_ref(v_xs_911_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___lam__0(lean_object* v_ctors_914_, lean_object* v_a_915_, lean_object* v___x_916_, lean_object* v_a_917_, uint8_t v___x_918_, uint8_t v___x_919_, lean_object* v_a_920_, lean_object* v_ys_921_, lean_object* v_x_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Array_idxOf_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__11(v_ctors_914_, v_a_915_);
if (lean_obj_tag(v___x_928_) == 1)
{
lean_object* v_val_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; lean_object* v___x_934_; 
lean_dec(v_a_915_);
v_val_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_val_929_);
lean_dec_ref_known(v___x_928_, 1);
lean_inc_ref(v_ys_921_);
v___x_930_ = lean_array_pop(v_ys_921_);
v___x_931_ = lean_array_get_borrowed(v___x_916_, v_a_917_, v_val_929_);
lean_dec(v_val_929_);
lean_inc(v___x_931_);
v___x_932_ = l_Lean_mkAppN(v___x_931_, v___x_930_);
lean_dec_ref(v___x_930_);
v___x_933_ = 1;
v___x_934_ = l_Lean_Meta_mkLambdaFVars(v_ys_921_, v___x_932_, v___x_918_, v___x_919_, v___x_918_, v___x_919_, v___x_933_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec_ref(v_ys_921_);
return v___x_934_;
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
lean_dec(v___x_928_);
v___x_935_ = lean_array_get_size(v_ys_921_);
v___x_936_ = lean_unsigned_to_nat(1u);
v___x_937_ = lean_nat_sub(v___x_935_, v___x_936_);
v___x_938_ = lean_array_get_borrowed(v___x_916_, v_ys_921_, v___x_937_);
lean_dec(v___x_937_);
v___x_939_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_a_915_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
if (lean_obj_tag(v___x_939_) == 0)
{
lean_object* v_a_940_; lean_object* v_cidx_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v_a_940_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_a_940_);
lean_dec_ref_known(v___x_939_, 1);
v_cidx_941_ = lean_ctor_get(v_a_940_, 2);
lean_inc(v_cidx_941_);
lean_dec(v_a_940_);
v___x_942_ = l_Lean_mkRawNatLit(v_cidx_941_);
v___x_943_ = l_Lean_mkHasNotBitProof(v___x_942_, v_a_920_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_945_; uint8_t v___x_946_; lean_object* v___x_947_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_a_944_);
lean_dec_ref_known(v___x_943_, 1);
lean_inc(v___x_938_);
v___x_945_ = l_Lean_Expr_app___override(v___x_938_, v_a_944_);
v___x_946_ = 1;
v___x_947_ = l_Lean_Meta_mkLambdaFVars(v_ys_921_, v___x_945_, v___x_918_, v___x_919_, v___x_918_, v___x_919_, v___x_946_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec_ref(v_ys_921_);
return v___x_947_;
}
else
{
lean_dec_ref(v_ys_921_);
return v___x_943_;
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref(v_ys_921_);
v_a_948_ = lean_ctor_get(v___x_939_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_939_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_939_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_939_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___lam__0___boxed(lean_object* v_ctors_956_, lean_object* v_a_957_, lean_object* v___x_958_, lean_object* v_a_959_, lean_object* v___x_960_, lean_object* v___x_961_, lean_object* v_a_962_, lean_object* v_ys_963_, lean_object* v_x_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
uint8_t v___x_22514__boxed_970_; uint8_t v___x_22515__boxed_971_; lean_object* v_res_972_; 
v___x_22514__boxed_970_ = lean_unbox(v___x_960_);
v___x_22515__boxed_971_ = lean_unbox(v___x_961_);
v_res_972_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___lam__0(v_ctors_956_, v_a_957_, v___x_958_, v_a_959_, v___x_22514__boxed_970_, v___x_22515__boxed_971_, v_a_962_, v_ys_963_, v_x_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec_ref(v_x_964_);
lean_dec_ref(v_a_962_);
lean_dec_ref(v_a_959_);
lean_dec_ref(v___x_958_);
lean_dec_ref(v_ctors_956_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13(lean_object* v_ctors_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_as_976_, lean_object* v_bs_977_, lean_object* v_i_978_, lean_object* v_cs_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_985_ = lean_array_get_size(v_as_976_);
v___x_986_ = lean_nat_dec_lt(v_i_978_, v___x_985_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; 
lean_dec(v_i_978_);
lean_dec_ref(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec_ref(v_ctors_973_);
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v_cs_979_);
return v___x_987_;
}
else
{
lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_988_ = lean_array_get_size(v_bs_977_);
v___x_989_ = lean_nat_dec_lt(v_i_978_, v___x_988_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; 
lean_dec(v_i_978_);
lean_dec_ref(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec_ref(v_ctors_973_);
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v_cs_979_);
return v___x_990_;
}
else
{
lean_object* v___x_991_; uint8_t v___x_992_; lean_object* v_a_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___f_996_; lean_object* v_b_997_; lean_object* v___x_998_; 
v___x_991_ = l_Lean_instInhabitedExpr;
v___x_992_ = 0;
v_a_993_ = lean_array_fget_borrowed(v_as_976_, v_i_978_);
v___x_994_ = lean_box(v___x_992_);
v___x_995_ = lean_box(v___x_989_);
lean_inc_ref(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_993_);
lean_inc_ref(v_ctors_973_);
v___f_996_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___lam__0___boxed), 14, 7);
lean_closure_set(v___f_996_, 0, v_ctors_973_);
lean_closure_set(v___f_996_, 1, v_a_993_);
lean_closure_set(v___f_996_, 2, v___x_991_);
lean_closure_set(v___f_996_, 3, v_a_974_);
lean_closure_set(v___f_996_, 4, v___x_994_);
lean_closure_set(v___f_996_, 5, v___x_995_);
lean_closure_set(v___f_996_, 6, v_a_975_);
v_b_997_ = lean_array_fget_borrowed(v_bs_977_, v_i_978_);
lean_inc(v_b_997_);
v___x_998_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg(v_b_997_, v___f_996_, v___x_992_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_998_, 1);
v___x_1000_ = lean_unsigned_to_nat(1u);
v___x_1001_ = lean_nat_add(v_i_978_, v___x_1000_);
lean_dec(v_i_978_);
v___x_1002_ = lean_array_push(v_cs_979_, v_a_999_);
v_i_978_ = v___x_1001_;
v_cs_979_ = v___x_1002_;
goto _start;
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec_ref(v_cs_979_);
lean_dec(v_i_978_);
lean_dec_ref(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec_ref(v_ctors_973_);
v_a_1004_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_998_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_998_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13___boxed(lean_object* v_ctors_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_as_1015_, lean_object* v_bs_1016_, lean_object* v_i_1017_, lean_object* v_cs_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13(v_ctors_1012_, v_a_1013_, v_a_1014_, v_as_1015_, v_bs_1016_, v_i_1017_, v_cs_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec_ref(v_bs_1016_);
lean_dec_ref(v_as_1015_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___lam__0(lean_object* v_k_1025_, lean_object* v_b_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; 
lean_inc(v___y_1030_);
lean_inc_ref(v___y_1029_);
lean_inc(v___y_1028_);
lean_inc_ref(v___y_1027_);
v___x_1032_ = lean_apply_6(v_k_1025_, v_b_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, lean_box(0));
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___lam__0___boxed(lean_object* v_k_1033_, lean_object* v_b_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___lam__0(v_k_1033_, v_b_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg(lean_object* v_name_1041_, uint8_t v_bi_1042_, lean_object* v_type_1043_, lean_object* v_k_1044_, uint8_t v_kind_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___f_1051_; lean_object* v___x_1052_; 
v___f_1051_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1051_, 0, v_k_1044_);
v___x_1052_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1041_, v_bi_1042_, v_type_1043_, v___f_1051_, v_kind_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
v_a_1061_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1052_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1052_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg___boxed(lean_object* v_name_1069_, lean_object* v_bi_1070_, lean_object* v_type_1071_, lean_object* v_k_1072_, lean_object* v_kind_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
uint8_t v_bi_boxed_1079_; uint8_t v_kind_boxed_1080_; lean_object* v_res_1081_; 
v_bi_boxed_1079_ = lean_unbox(v_bi_1070_);
v_kind_boxed_1080_ = lean_unbox(v_kind_1073_);
v_res_1081_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg(v_name_1069_, v_bi_boxed_1079_, v_type_1071_, v_k_1072_, v_kind_boxed_1080_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg(lean_object* v_name_1082_, lean_object* v_type_1083_, lean_object* v_k_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
uint8_t v___x_1090_; uint8_t v___x_1091_; lean_object* v___x_1092_; 
v___x_1090_ = 0;
v___x_1091_ = 0;
v___x_1092_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg(v_name_1082_, v___x_1090_, v_type_1083_, v_k_1084_, v___x_1091_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg___boxed(lean_object* v_name_1093_, lean_object* v_type_1094_, lean_object* v_k_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg(v_name_1093_, v_type_1094_, v_k_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__9(size_t v_sz_1102_, size_t v_i_1103_, lean_object* v_bs_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
uint8_t v___x_1110_; 
v___x_1110_ = lean_usize_dec_lt(v_i_1103_, v_sz_1102_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1111_, 0, v_bs_1104_);
return v___x_1111_;
}
else
{
lean_object* v_v_1112_; lean_object* v___x_1113_; lean_object* v_bs_x27_1114_; lean_object* v___x_1115_; 
v_v_1112_ = lean_array_uget(v_bs_1104_, v_i_1103_);
v___x_1113_ = lean_unsigned_to_nat(0u);
v_bs_x27_1114_ = lean_array_uset(v_bs_1104_, v_i_1103_, v___x_1113_);
v___x_1115_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_v_1112_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v_cidx_1117_; size_t v___x_1118_; size_t v___x_1119_; lean_object* v___x_1120_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1115_, 1);
v_cidx_1117_ = lean_ctor_get(v_a_1116_, 2);
lean_inc(v_cidx_1117_);
lean_dec(v_a_1116_);
v___x_1118_ = ((size_t)1ULL);
v___x_1119_ = lean_usize_add(v_i_1103_, v___x_1118_);
v___x_1120_ = lean_array_uset(v_bs_x27_1114_, v_i_1103_, v_cidx_1117_);
v_i_1103_ = v___x_1119_;
v_bs_1104_ = v___x_1120_;
goto _start;
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec_ref(v_bs_x27_1114_);
v_a_1122_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1115_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1115_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__9___boxed(lean_object* v_sz_1130_, lean_object* v_i_1131_, lean_object* v_bs_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
size_t v_sz_boxed_1138_; size_t v_i_boxed_1139_; lean_object* v_res_1140_; 
v_sz_boxed_1138_ = lean_unbox_usize(v_sz_1130_);
lean_dec(v_sz_1130_);
v_i_boxed_1139_ = lean_unbox_usize(v_i_1131_);
lean_dec(v_i_1131_);
v_res_1140_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__9(v_sz_boxed_1138_, v_i_boxed_1139_, v_bs_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(lean_object* v___x_1141_, size_t v_sz_1142_, size_t v_i_1143_, lean_object* v_bs_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
uint8_t v___x_1150_; 
v___x_1150_ = lean_usize_dec_lt(v_i_1143_, v_sz_1142_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; 
v___x_1151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1151_, 0, v_bs_1144_);
return v___x_1151_;
}
else
{
lean_object* v___x_1152_; lean_object* v_v_1153_; lean_object* v___x_1154_; lean_object* v_bs_x27_1155_; lean_object* v_a_1157_; lean_object* v___x_1162_; 
v___x_1152_ = l_Lean_instInhabitedExpr;
v_v_1153_ = lean_array_uget(v_bs_1144_, v_i_1143_);
v___x_1154_ = lean_unsigned_to_nat(0u);
v_bs_x27_1155_ = lean_array_uset(v_bs_1144_, v_i_1143_, v___x_1154_);
v___x_1162_ = l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0(v_v_1153_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v_cidx_1164_; lean_object* v_start_1165_; lean_object* v_stop_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v_cidx_1164_ = lean_ctor_get(v_a_1163_, 2);
lean_inc(v_cidx_1164_);
lean_dec(v_a_1163_);
v_start_1165_ = lean_ctor_get(v___x_1141_, 1);
v_stop_1166_ = lean_ctor_get(v___x_1141_, 2);
v___x_1167_ = lean_nat_sub(v_stop_1166_, v_start_1165_);
v___x_1168_ = lean_nat_dec_lt(v_cidx_1164_, v___x_1167_);
lean_dec(v___x_1167_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; 
lean_dec(v_cidx_1164_);
v___x_1169_ = l_outOfBounds___redArg(v___x_1152_);
v_a_1157_ = v___x_1169_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Subarray_get___redArg(v___x_1141_, v_cidx_1164_);
lean_dec(v_cidx_1164_);
v_a_1157_ = v___x_1170_;
goto v___jp_1156_;
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_dec_ref(v_bs_x27_1155_);
v_a_1171_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1162_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1162_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
v___jp_1156_:
{
size_t v___x_1158_; size_t v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = ((size_t)1ULL);
v___x_1159_ = lean_usize_add(v_i_1143_, v___x_1158_);
v___x_1160_ = lean_array_uset(v_bs_x27_1155_, v_i_1143_, v_a_1157_);
v_i_1143_ = v___x_1159_;
v_bs_1144_ = v___x_1160_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8___boxed(lean_object* v___x_1179_, lean_object* v_sz_1180_, lean_object* v_i_1181_, lean_object* v_bs_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
size_t v_sz_boxed_1188_; size_t v_i_boxed_1189_; lean_object* v_res_1190_; 
v_sz_boxed_1188_ = lean_unbox_usize(v_sz_1180_);
lean_dec(v_sz_1180_);
v_i_boxed_1189_ = lean_unbox_usize(v_i_1181_);
lean_dec(v_i_1181_);
v_res_1190_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(v___x_1179_, v_sz_boxed_1188_, v_i_boxed_1189_, v_bs_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec_ref(v___x_1179_);
return v_res_1190_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__5));
v___x_1201_ = l_Lean_stringToMessageData(v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2(lean_object* v_numParams_1202_, lean_object* v___x_1203_, lean_object* v_numIndices_1204_, uint8_t v___x_1205_, lean_object* v_ctors_1206_, lean_object* v___x_1207_, lean_object* v___x_1208_, lean_object* v_a_1209_, lean_object* v_ctors_1210_, lean_object* v___x_1211_, lean_object* v_xs_1212_, lean_object* v_x_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1327_ = lean_array_get_size(v_xs_1212_);
v___x_1328_ = lean_unsigned_to_nat(1u);
v___x_1329_ = lean_nat_add(v_numParams_1202_, v___x_1328_);
v___x_1330_ = lean_nat_add(v___x_1329_, v_numIndices_1204_);
lean_dec(v___x_1329_);
v___x_1331_ = lean_nat_add(v___x_1330_, v___x_1328_);
lean_dec(v___x_1330_);
v___x_1332_ = l_List_lengthTR___redArg(v_ctors_1210_);
v___x_1333_ = lean_nat_add(v___x_1331_, v___x_1332_);
lean_dec(v___x_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_nat_dec_eq(v___x_1327_, v___x_1333_);
lean_dec(v___x_1333_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref(v_xs_1212_);
lean_dec(v_ctors_1210_);
lean_dec(v___x_1208_);
lean_dec(v___x_1207_);
lean_dec_ref(v_ctors_1206_);
lean_dec(v_numParams_1202_);
v___x_1335_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6, &l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6_once, _init_l_Lean_Meta_mkSparseCasesOn___lam__2___closed__6);
v___x_1336_ = l_Lean_MessageData_ofConstName(v___x_1211_, v___x_1334_);
v___x_1337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1335_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
v___x_1338_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0);
v___x_1339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1337_);
lean_ctor_set(v___x_1339_, 1, v___x_1338_);
v___x_1340_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___x_1339_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1340_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1340_);
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
else
{
lean_dec(v___x_1211_);
v___y_1220_ = v___y_1214_;
v___y_1221_ = v___y_1215_;
v___y_1222_ = v___y_1216_;
v___y_1223_ = v___y_1217_;
goto v___jp_1219_;
}
v___jp_1219_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___f_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; size_t v_sz_1241_; size_t v___x_1242_; lean_object* v___x_1243_; 
v___x_1224_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1202_);
lean_inc_ref_n(v_xs_1212_, 2);
v___x_1225_ = l_Array_toSubarray___redArg(v_xs_1212_, v___x_1224_, v_numParams_1202_);
v___x_1226_ = lean_array_get(v___x_1203_, v_xs_1212_, v_numParams_1202_);
v___x_1227_ = lean_unsigned_to_nat(1u);
v___x_1228_ = lean_nat_add(v_numParams_1202_, v___x_1227_);
lean_dec(v_numParams_1202_);
v___x_1229_ = lean_nat_add(v___x_1228_, v_numIndices_1204_);
lean_inc(v___x_1229_);
v___x_1230_ = l_Array_toSubarray___redArg(v_xs_1212_, v___x_1228_, v___x_1229_);
v___x_1231_ = lean_array_get(v___x_1203_, v_xs_1212_, v___x_1229_);
v___x_1232_ = l_Subarray_copy___redArg(v___x_1230_);
v___x_1233_ = lean_mk_empty_array_with_capacity(v___x_1227_);
lean_inc(v___x_1231_);
lean_inc_ref_n(v___x_1233_, 2);
v___x_1234_ = lean_array_push(v___x_1233_, v___x_1231_);
lean_inc_ref(v___x_1232_);
v___x_1235_ = l_Array_append___redArg(v___x_1232_, v___x_1234_);
v___x_1236_ = lean_box(v___x_1205_);
lean_inc_ref(v___x_1235_);
lean_inc(v___x_1226_);
v___f_1237_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSparseCasesOn___lam__1___boxed), 10, 4);
lean_closure_set(v___f_1237_, 0, v___x_1233_);
lean_closure_set(v___f_1237_, 1, v___x_1226_);
lean_closure_set(v___f_1237_, 2, v___x_1235_);
lean_closure_set(v___f_1237_, 3, v___x_1236_);
v___x_1238_ = lean_nat_add(v___x_1229_, v___x_1227_);
lean_dec(v___x_1229_);
v___x_1239_ = lean_array_get_size(v_xs_1212_);
v___x_1240_ = l_Array_toSubarray___redArg(v_xs_1212_, v___x_1238_, v___x_1239_);
v_sz_1241_ = lean_array_size(v_ctors_1206_);
v___x_1242_ = ((size_t)0ULL);
lean_inc_ref(v_ctors_1206_);
v___x_1243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__8(v___x_1240_, v_sz_1241_, v___x_1242_, v_ctors_1206_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec_ref(v___x_1240_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1245_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref_known(v___x_1243_, 1);
lean_inc_ref(v_ctors_1206_);
v___x_1245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_mkSparseCasesOn_spec__9(v_sz_1241_, v___x_1242_, v_ctors_1206_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref_known(v___x_1245_, 1);
v___x_1247_ = l_Lean_mkConst(v___x_1207_, v___x_1208_);
v___x_1248_ = l_Subarray_copy___redArg(v___x_1225_);
lean_inc_ref(v___x_1248_);
v___x_1249_ = l_Array_append___redArg(v___x_1248_, v___x_1232_);
v___x_1250_ = l_Array_append___redArg(v___x_1249_, v___x_1234_);
v___x_1251_ = l_Lean_mkAppN(v___x_1247_, v___x_1250_);
lean_dec_ref(v___x_1250_);
v___x_1252_ = l_Lean_mkHasNotBit(v___x_1251_, v_a_1246_);
v___x_1253_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__1));
v___x_1254_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg(v___x_1253_, v___x_1252_, v___f_1237_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___x_1254_, 1);
v___x_1256_ = l_Lean_ConstantInfo_value_x21(v_a_1209_, v___x_1205_);
v___x_1257_ = l_Lean_mkAppN(v___x_1256_, v___x_1248_);
v___x_1258_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__3));
v___x_1259_ = l_Lean_Core_mkFreshUserName(v___x_1258_, v___y_1222_, v___y_1223_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_a_1260_; uint8_t v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; uint8_t v___x_1265_; lean_object* v___x_1266_; 
v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_a_1260_);
lean_dec_ref_known(v___x_1259_, 1);
v___x_1261_ = 0;
lean_inc(v___x_1226_);
v___x_1262_ = l_Lean_mkAppN(v___x_1226_, v___x_1235_);
v___x_1263_ = l_Lean_mkForall(v_a_1260_, v___x_1261_, v_a_1255_, v___x_1262_);
v___x_1264_ = 1;
v___x_1265_ = 1;
v___x_1266_ = l_Lean_Meta_mkLambdaFVars(v___x_1235_, v___x_1263_, v___x_1205_, v___x_1264_, v___x_1205_, v___x_1264_, v___x_1265_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec_ref(v___x_1235_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___x_1266_, 1);
v___x_1268_ = l_Lean_Expr_app___override(v___x_1257_, v_a_1267_);
v___x_1269_ = l_Lean_mkAppN(v___x_1268_, v___x_1232_);
v___x_1270_ = l_Lean_Expr_app___override(v___x_1269_, v___x_1231_);
v___x_1271_ = l_List_lengthTR___redArg(v_ctors_1210_);
lean_inc_ref(v___x_1270_);
v___x_1272_ = l_Lean_Meta_inferArgumentTypesN(v___x_1271_, v___x_1270_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1272_, 1);
v___x_1274_ = lean_array_mk(v_ctors_1210_);
v___x_1275_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__2___closed__4));
lean_inc(v_a_1244_);
v___x_1276_ = l_Array_zipWithMAux___at___00Lean_Meta_mkSparseCasesOn_spec__13(v_ctors_1206_, v_a_1244_, v_a_1246_, v___x_1274_, v_a_1273_, v___x_1224_, v___x_1275_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec(v_a_1273_);
lean_dec_ref(v___x_1274_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1276_, 1);
v___x_1278_ = l_Lean_mkAppN(v___x_1270_, v_a_1277_);
lean_dec(v_a_1277_);
v___x_1279_ = l_Lean_Core_betaReduce(v___x_1278_, v___y_1222_, v___y_1223_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v___x_1281_ = lean_array_push(v___x_1233_, v___x_1226_);
v___x_1282_ = l_Array_append___redArg(v___x_1248_, v___x_1281_);
lean_dec_ref(v___x_1281_);
v___x_1283_ = l_Array_append___redArg(v___x_1282_, v___x_1232_);
lean_dec_ref(v___x_1232_);
v___x_1284_ = l_Array_append___redArg(v___x_1283_, v___x_1234_);
lean_dec_ref(v___x_1234_);
v___x_1285_ = l_Array_append___redArg(v___x_1284_, v_a_1244_);
lean_dec(v_a_1244_);
v___x_1286_ = l_Lean_Meta_mkLambdaFVars(v___x_1285_, v_a_1280_, v___x_1205_, v___x_1264_, v___x_1205_, v___x_1264_, v___x_1265_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec_ref(v___x_1285_);
return v___x_1286_;
}
else
{
lean_dec_ref(v___x_1248_);
lean_dec(v_a_1244_);
lean_dec_ref(v___x_1234_);
lean_dec_ref(v___x_1233_);
lean_dec_ref(v___x_1232_);
lean_dec(v___x_1226_);
return v___x_1279_;
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1248_);
lean_dec(v_a_1244_);
lean_dec_ref(v___x_1234_);
lean_dec_ref(v___x_1233_);
lean_dec_ref(v___x_1232_);
lean_dec(v___x_1226_);
v_a_1287_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1276_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1276_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec_ref(v___x_1270_);
lean_dec_ref(v___x_1248_);
lean_dec(v_a_1246_);
lean_dec(v_a_1244_);
lean_dec_ref(v___x_1234_);
lean_dec_ref(v___x_1233_);
lean_dec_ref(v___x_1232_);
lean_dec(v___x_1226_);
lean_dec(v_ctors_1210_);
lean_dec_ref(v_ctors_1206_);
v_a_1295_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1272_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1272_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
else
{
lean_dec_ref(v___x_1257_);
lean_dec_ref(v___x_1248_);
lean_dec(v_a_1246_);
lean_dec(v_a_1244_);
lean_dec_ref(v___x_1234_);
lean_dec_ref(v___x_1233_);
lean_dec_ref(v___x_1232_);
lean_dec(v___x_1231_);
lean_dec(v___x_1226_);
lean_dec(v_ctors_1210_);
lean_dec_ref(v_ctors_1206_);
return v___x_1266_;
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec_ref(v___x_1257_);
lean_dec(v_a_1255_);
lean_dec_ref(v___x_1248_);
lean_dec(v_a_1246_);
lean_dec(v_a_1244_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v___x_1234_);
lean_dec_ref(v___x_1233_);
lean_dec_ref(v___x_1232_);
lean_dec(v___x_1231_);
lean_dec(v___x_1226_);
lean_dec(v_ctors_1210_);
lean_dec_ref(v_ctors_1206_);
v_a_1303_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1259_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1259_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
else
{
lean_dec_ref(v___x_1248_);
lean_dec(v_a_1246_);
lean_dec(v_a_1244_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v___x_1234_);
lean_dec_ref(v___x_1233_);
lean_dec_ref(v___x_1232_);
lean_dec(v___x_1231_);
lean_dec(v___x_1226_);
lean_dec(v_ctors_1210_);
lean_dec_ref(v_ctors_1206_);
return v___x_1254_;
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec(v_a_1244_);
lean_dec_ref(v___f_1237_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v___x_1234_);
lean_dec_ref(v___x_1233_);
lean_dec_ref(v___x_1232_);
lean_dec(v___x_1231_);
lean_dec(v___x_1226_);
lean_dec_ref(v___x_1225_);
lean_dec(v_ctors_1210_);
lean_dec(v___x_1208_);
lean_dec(v___x_1207_);
lean_dec_ref(v_ctors_1206_);
v_a_1311_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1245_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1245_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec_ref(v___f_1237_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v___x_1234_);
lean_dec_ref(v___x_1233_);
lean_dec_ref(v___x_1232_);
lean_dec(v___x_1231_);
lean_dec(v___x_1226_);
lean_dec_ref(v___x_1225_);
lean_dec(v_ctors_1210_);
lean_dec(v___x_1208_);
lean_dec(v___x_1207_);
lean_dec_ref(v_ctors_1206_);
v_a_1319_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1243_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1243_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___lam__2___boxed(lean_object** _args){
lean_object* v_numParams_1349_ = _args[0];
lean_object* v___x_1350_ = _args[1];
lean_object* v_numIndices_1351_ = _args[2];
lean_object* v___x_1352_ = _args[3];
lean_object* v_ctors_1353_ = _args[4];
lean_object* v___x_1354_ = _args[5];
lean_object* v___x_1355_ = _args[6];
lean_object* v_a_1356_ = _args[7];
lean_object* v_ctors_1357_ = _args[8];
lean_object* v___x_1358_ = _args[9];
lean_object* v_xs_1359_ = _args[10];
lean_object* v_x_1360_ = _args[11];
lean_object* v___y_1361_ = _args[12];
lean_object* v___y_1362_ = _args[13];
lean_object* v___y_1363_ = _args[14];
lean_object* v___y_1364_ = _args[15];
lean_object* v___y_1365_ = _args[16];
_start:
{
uint8_t v___x_22901__boxed_1366_; lean_object* v_res_1367_; 
v___x_22901__boxed_1366_ = lean_unbox(v___x_1352_);
v_res_1367_ = l_Lean_Meta_mkSparseCasesOn___lam__2(v_numParams_1349_, v___x_1350_, v_numIndices_1351_, v___x_22901__boxed_1366_, v_ctors_1353_, v___x_1354_, v___x_1355_, v_a_1356_, v_ctors_1357_, v___x_1358_, v_xs_1359_, v_x_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec_ref(v_x_1360_);
lean_dec_ref(v_a_1356_);
lean_dec(v_numIndices_1351_);
lean_dec_ref(v___x_1350_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg(lean_object* v_ref_1368_, lean_object* v_msg_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v_toCold_1375_; lean_object* v_currRecDepth_1376_; lean_object* v_ref_1377_; uint16_t v_optionFlags_1378_; uint8_t v_suppressElabErrors_1379_; uint8_t v_isRecordingDeps_1380_; lean_object* v_ref_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_toCold_1375_ = lean_ctor_get(v___y_1372_, 0);
v_currRecDepth_1376_ = lean_ctor_get(v___y_1372_, 1);
v_ref_1377_ = lean_ctor_get(v___y_1372_, 2);
v_optionFlags_1378_ = lean_ctor_get_uint16(v___y_1372_, sizeof(void*)*3);
v_suppressElabErrors_1379_ = lean_ctor_get_uint8(v___y_1372_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1380_ = lean_ctor_get_uint8(v___y_1372_, sizeof(void*)*3 + 3);
v_ref_1381_ = l_Lean_replaceRef(v_ref_1368_, v_ref_1377_);
lean_inc(v_currRecDepth_1376_);
lean_inc_ref(v_toCold_1375_);
v___x_1382_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1382_, 0, v_toCold_1375_);
lean_ctor_set(v___x_1382_, 1, v_currRecDepth_1376_);
lean_ctor_set(v___x_1382_, 2, v_ref_1381_);
lean_ctor_set_uint16(v___x_1382_, sizeof(void*)*3, v_optionFlags_1378_);
lean_ctor_set_uint8(v___x_1382_, sizeof(void*)*3 + 2, v_suppressElabErrors_1379_);
lean_ctor_set_uint8(v___x_1382_, sizeof(void*)*3 + 3, v_isRecordingDeps_1380_);
v___x_1383_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v_msg_1369_, v___y_1370_, v___y_1371_, v___x_1382_, v___y_1373_);
lean_dec_ref_known(v___x_1382_, 3);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg___boxed(lean_object* v_ref_1384_, lean_object* v_msg_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg(v_ref_1384_, v_msg_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v_ref_1384_);
return v_res_1391_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0(void){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_);
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
return v___x_1393_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__1(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1394_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1395_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0);
v___x_1396_ = lean_unsigned_to_nat(0u);
v___x_1397_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
lean_ctor_set(v___x_1397_, 1, v___x_1396_);
lean_ctor_set(v___x_1397_, 2, v___x_1396_);
lean_ctor_set(v___x_1397_, 3, v___x_1396_);
lean_ctor_set(v___x_1397_, 4, v___x_1395_);
lean_ctor_set(v___x_1397_, 5, v___x_1395_);
lean_ctor_set(v___x_1397_, 6, v___x_1395_);
lean_ctor_set(v___x_1397_, 7, v___x_1395_);
lean_ctor_set(v___x_1397_, 8, v___x_1395_);
lean_ctor_set(v___x_1397_, 9, v___x_1395_);
lean_ctor_set(v___x_1397_, 10, v___x_1395_);
lean_ctor_set(v___x_1397_, 11, v___x_1394_);
return v___x_1397_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__2(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1398_ = lean_unsigned_to_nat(32u);
v___x_1399_ = lean_mk_empty_array_with_capacity(v___x_1398_);
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
return v___x_1400_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__3(void){
_start:
{
size_t v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1401_ = ((size_t)5ULL);
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = lean_unsigned_to_nat(32u);
v___x_1404_ = lean_mk_empty_array_with_capacity(v___x_1403_);
v___x_1405_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__2);
v___x_1406_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
lean_ctor_set(v___x_1406_, 1, v___x_1404_);
lean_ctor_set(v___x_1406_, 2, v___x_1402_);
lean_ctor_set(v___x_1406_, 3, v___x_1402_);
lean_ctor_set_usize(v___x_1406_, 4, v___x_1401_);
return v___x_1406_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__4(void){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1407_ = lean_box(1);
v___x_1408_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__3);
v___x_1409_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__0);
v___x_1410_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
lean_ctor_set(v___x_1410_, 1, v___x_1408_);
lean_ctor_set(v___x_1410_, 2, v___x_1407_);
return v___x_1410_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__5));
v___x_1413_ = l_Lean_stringToMessageData(v___x_1412_);
return v___x_1413_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__8(void){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__7));
v___x_1416_ = l_Lean_stringToMessageData(v___x_1415_);
return v___x_1416_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__10(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__9));
v___x_1419_ = l_Lean_stringToMessageData(v___x_1418_);
return v___x_1419_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__12(void){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__11));
v___x_1422_ = l_Lean_stringToMessageData(v___x_1421_);
return v___x_1422_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__14(void){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__13));
v___x_1425_ = l_Lean_stringToMessageData(v___x_1424_);
return v___x_1425_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__16(void){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1427_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__15));
v___x_1428_ = l_Lean_stringToMessageData(v___x_1427_);
return v___x_1428_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__18(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__17));
v___x_1431_ = l_Lean_stringToMessageData(v___x_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg(lean_object* v_msg_1432_, lean_object* v_declHint_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v_env_1438_; uint8_t v___x_1439_; 
v___x_1436_ = lean_box(0);
v___x_1437_ = lean_st_ref_get(v___y_1434_);
v_env_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc_ref(v_env_1438_);
lean_dec(v___x_1437_);
v___x_1439_ = l_Lean_Name_isAnonymous(v_declHint_1433_);
if (v___x_1439_ == 0)
{
uint8_t v_isExporting_1440_; 
v_isExporting_1440_ = lean_ctor_get_uint8(v_env_1438_, sizeof(void*)*13);
if (v_isExporting_1440_ == 0)
{
lean_object* v___x_1441_; 
lean_dec_ref(v_env_1438_);
lean_dec(v_declHint_1433_);
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v_msg_1432_);
return v___x_1441_;
}
else
{
lean_object* v___x_1442_; uint8_t v___x_1443_; 
lean_inc_ref(v_env_1438_);
v___x_1442_ = l_Lean_Environment_setExporting(v_env_1438_, v___x_1439_);
lean_inc(v_declHint_1433_);
lean_inc_ref(v___x_1442_);
v___x_1443_ = l_Lean_Environment_contains(v___x_1442_, v_declHint_1433_, v_isExporting_1440_);
if (v___x_1443_ == 0)
{
lean_object* v___x_1444_; 
lean_dec_ref(v___x_1442_);
lean_dec_ref(v_env_1438_);
lean_dec(v_declHint_1433_);
v___x_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1444_, 0, v_msg_1432_);
return v___x_1444_;
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v_c_1450_; lean_object* v___x_1451_; 
v___x_1445_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__1);
v___x_1446_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__4);
v___x_1447_ = l_Lean_Options_empty;
v___x_1448_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1442_);
lean_ctor_set(v___x_1448_, 1, v___x_1445_);
lean_ctor_set(v___x_1448_, 2, v___x_1446_);
lean_ctor_set(v___x_1448_, 3, v___x_1447_);
lean_inc(v_declHint_1433_);
v___x_1449_ = l_Lean_MessageData_ofConstName(v_declHint_1433_, v___x_1439_);
v_c_1450_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1450_, 0, v___x_1448_);
lean_ctor_set(v_c_1450_, 1, v___x_1449_);
v___x_1451_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1438_, v_declHint_1433_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_dec_ref(v_env_1438_);
lean_dec(v_declHint_1433_);
v___x_1452_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6);
v___x_1453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
lean_ctor_set(v___x_1453_, 1, v_c_1450_);
v___x_1454_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__8);
v___x_1455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1453_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = l_Lean_MessageData_note(v___x_1455_);
v___x_1457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1457_, 0, v_msg_1432_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___x_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
return v___x_1458_;
}
else
{
lean_object* v_val_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1493_; 
v_val_1459_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1461_ = v___x_1451_;
v_isShared_1462_ = v_isSharedCheck_1493_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_val_1459_);
lean_dec(v___x_1451_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1493_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; lean_object* v_moduleNames_1464_; lean_object* v_mod_1465_; uint8_t v___x_1466_; 
v___x_1463_ = l_Lean_Environment_header(v_env_1438_);
lean_dec_ref(v_env_1438_);
v_moduleNames_1464_ = lean_ctor_get(v___x_1463_, 4);
lean_inc_ref(v_moduleNames_1464_);
lean_dec_ref(v___x_1463_);
v_mod_1465_ = lean_array_get(v___x_1436_, v_moduleNames_1464_, v_val_1459_);
lean_dec(v_val_1459_);
lean_dec_ref(v_moduleNames_1464_);
v___x_1466_ = l_Lean_isPrivateName(v_declHint_1433_);
lean_dec(v_declHint_1433_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1478_; 
v___x_1467_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__10);
v___x_1468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
lean_ctor_set(v___x_1468_, 1, v_c_1450_);
v___x_1469_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__12);
v___x_1470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1468_);
lean_ctor_set(v___x_1470_, 1, v___x_1469_);
v___x_1471_ = l_Lean_MessageData_ofName(v_mod_1465_);
v___x_1472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1470_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
v___x_1473_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__14);
v___x_1474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1472_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
v___x_1475_ = l_Lean_MessageData_note(v___x_1474_);
v___x_1476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1476_, 0, v_msg_1432_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set_tag(v___x_1461_, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1476_);
v___x_1478_ = v___x_1461_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1480_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__6);
v___x_1481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
lean_ctor_set(v___x_1481_, 1, v_c_1450_);
v___x_1482_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__16);
v___x_1483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1481_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
v___x_1484_ = l_Lean_MessageData_ofName(v_mod_1465_);
v___x_1485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1483_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
v___x_1486_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___closed__18);
v___x_1487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1485_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = l_Lean_MessageData_note(v___x_1487_);
v___x_1489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1489_, 0, v_msg_1432_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set_tag(v___x_1461_, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1489_);
v___x_1491_ = v___x_1461_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1494_; 
lean_dec_ref(v_env_1438_);
lean_dec(v_declHint_1433_);
v___x_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1494_, 0, v_msg_1432_);
return v___x_1494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg___boxed(lean_object* v_msg_1495_, lean_object* v_declHint_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg(v_msg_1495_, v_declHint_1496_, v___y_1497_);
lean_dec(v___y_1497_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33(lean_object* v_msg_1500_, lean_object* v_declHint_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v___x_1507_; lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1517_; 
v___x_1507_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg(v_msg_1500_, v_declHint_1501_, v___y_1505_);
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1510_ = v___x_1507_;
v_isShared_1511_ = v_isSharedCheck_1517_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1507_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1517_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1512_ = l_Lean_unknownIdentifierMessageTag;
v___x_1513_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
lean_ctor_set(v___x_1513_, 1, v_a_1508_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v___x_1513_);
v___x_1515_ = v___x_1510_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33___boxed(lean_object* v_msg_1518_, lean_object* v_declHint_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33(v_msg_1518_, v_declHint_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg(lean_object* v_ref_1526_, lean_object* v_msg_1527_, lean_object* v_declHint_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___x_1534_; lean_object* v_a_1535_; lean_object* v___x_1536_; 
v___x_1534_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33(v_msg_1527_, v_declHint_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref(v___x_1534_);
v___x_1536_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg(v_ref_1526_, v_a_1535_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg___boxed(lean_object* v_ref_1537_, lean_object* v_msg_1538_, lean_object* v_declHint_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg(v_ref_1537_, v_msg_1538_, v_declHint_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v_ref_1537_);
return v_res_1545_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__0));
v___x_1548_ = l_Lean_stringToMessageData(v___x_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg(lean_object* v_ref_1549_, lean_object* v_constName_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___x_1556_; uint8_t v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1556_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___closed__1);
v___x_1557_ = 0;
lean_inc(v_constName_1550_);
v___x_1558_ = l_Lean_MessageData_ofConstName(v_constName_1550_, v___x_1557_);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1556_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg(v_ref_1549_, v___x_1561_, v_constName_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg___boxed(lean_object* v_ref_1563_, lean_object* v_constName_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg(v_ref_1563_, v_constName_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v_ref_1563_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg(lean_object* v_constName_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v_ref_1577_; lean_object* v___x_1578_; 
v_ref_1577_ = lean_ctor_get(v___y_1574_, 2);
v___x_1578_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg(v_ref_1577_, v_constName_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg___boxed(lean_object* v_constName_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg(v_constName_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6(lean_object* v_constName_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
lean_object* v___x_1592_; lean_object* v_env_1593_; uint8_t v___x_1594_; lean_object* v___x_1595_; 
v___x_1592_ = lean_st_ref_get(v___y_1590_);
v_env_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc_ref(v_env_1593_);
lean_dec(v___x_1592_);
v___x_1594_ = 0;
lean_inc(v_constName_1586_);
v___x_1595_ = l_Lean_Environment_find_x3f(v_env_1593_, v_constName_1586_, v___x_1594_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg(v_constName_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_);
return v___x_1596_;
}
else
{
lean_object* v_val_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1604_; 
lean_dec(v_constName_1586_);
v_val_1597_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1599_ = v___x_1595_;
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_val_1597_);
lean_dec(v___x_1595_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1604_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
lean_ctor_set_tag(v___x_1599_, 0);
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_val_1597_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6___boxed(lean_object* v_constName_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6(v_constName_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
return v_res_1611_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = lean_obj_once(&l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_);
v___x_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
return v___x_1613_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1(void){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0);
v___x_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
return v___x_1615_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__0);
v___x_1617_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
lean_ctor_set(v___x_1617_, 2, v___x_1616_);
lean_ctor_set(v___x_1617_, 3, v___x_1616_);
lean_ctor_set(v___x_1617_, 4, v___x_1616_);
lean_ctor_set(v___x_1617_, 5, v___x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg(lean_object* v_declName_1618_, uint8_t v_s_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v___x_1623_; lean_object* v_env_1624_; lean_object* v_nextMacroScope_1625_; lean_object* v_ngen_1626_; lean_object* v_auxDeclNGen_1627_; lean_object* v_traceState_1628_; lean_object* v_recordedDeps_1629_; lean_object* v_messages_1630_; lean_object* v_infoState_1631_; lean_object* v_snapshotTasks_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1661_; 
v___x_1623_ = lean_st_ref_take(v___y_1621_);
v_env_1624_ = lean_ctor_get(v___x_1623_, 0);
v_nextMacroScope_1625_ = lean_ctor_get(v___x_1623_, 1);
v_ngen_1626_ = lean_ctor_get(v___x_1623_, 2);
v_auxDeclNGen_1627_ = lean_ctor_get(v___x_1623_, 3);
v_traceState_1628_ = lean_ctor_get(v___x_1623_, 4);
v_recordedDeps_1629_ = lean_ctor_get(v___x_1623_, 6);
v_messages_1630_ = lean_ctor_get(v___x_1623_, 7);
v_infoState_1631_ = lean_ctor_get(v___x_1623_, 8);
v_snapshotTasks_1632_ = lean_ctor_get(v___x_1623_, 9);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1661_ == 0)
{
lean_object* v_unused_1662_; 
v_unused_1662_ = lean_ctor_get(v___x_1623_, 5);
lean_dec(v_unused_1662_);
v___x_1634_ = v___x_1623_;
v_isShared_1635_ = v_isSharedCheck_1661_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_snapshotTasks_1632_);
lean_inc(v_infoState_1631_);
lean_inc(v_messages_1630_);
lean_inc(v_recordedDeps_1629_);
lean_inc(v_traceState_1628_);
lean_inc(v_auxDeclNGen_1627_);
lean_inc(v_ngen_1626_);
lean_inc(v_nextMacroScope_1625_);
lean_inc(v_env_1624_);
lean_dec(v___x_1623_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1661_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
uint8_t v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1636_ = 0;
v___x_1637_ = lean_box(0);
v___x_1638_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1624_, v_declName_1618_, v_s_1619_, v___x_1636_, v___x_1637_);
v___x_1639_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 5, v___x_1639_);
lean_ctor_set(v___x_1634_, 0, v___x_1638_);
v___x_1641_ = v___x_1634_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1638_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_nextMacroScope_1625_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_ngen_1626_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v_auxDeclNGen_1627_);
lean_ctor_set(v_reuseFailAlloc_1660_, 4, v_traceState_1628_);
lean_ctor_set(v_reuseFailAlloc_1660_, 5, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1660_, 6, v_recordedDeps_1629_);
lean_ctor_set(v_reuseFailAlloc_1660_, 7, v_messages_1630_);
lean_ctor_set(v_reuseFailAlloc_1660_, 8, v_infoState_1631_);
lean_ctor_set(v_reuseFailAlloc_1660_, 9, v_snapshotTasks_1632_);
v___x_1641_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v_mctx_1644_; lean_object* v_zetaDeltaFVarIds_1645_; lean_object* v_postponed_1646_; lean_object* v_diag_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1658_; 
v___x_1642_ = lean_st_ref_put(v___y_1621_, v___x_1641_);
v___x_1643_ = lean_st_ref_take(v___y_1620_);
v_mctx_1644_ = lean_ctor_get(v___x_1643_, 0);
v_zetaDeltaFVarIds_1645_ = lean_ctor_get(v___x_1643_, 2);
v_postponed_1646_ = lean_ctor_get(v___x_1643_, 3);
v_diag_1647_ = lean_ctor_get(v___x_1643_, 4);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; 
v_unused_1659_ = lean_ctor_get(v___x_1643_, 1);
lean_dec(v_unused_1659_);
v___x_1649_ = v___x_1643_;
v_isShared_1650_ = v_isSharedCheck_1658_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_diag_1647_);
lean_inc(v_postponed_1646_);
lean_inc(v_zetaDeltaFVarIds_1645_);
lean_inc(v_mctx_1644_);
lean_dec(v___x_1643_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1658_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1651_ = lean_box(0);
v___x_1652_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 1, v___x_1652_);
v___x_1654_ = v___x_1649_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_mctx_1644_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v___x_1652_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v_zetaDeltaFVarIds_1645_);
lean_ctor_set(v_reuseFailAlloc_1657_, 3, v_postponed_1646_);
lean_ctor_set(v_reuseFailAlloc_1657_, 4, v_diag_1647_);
v___x_1654_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1655_ = lean_st_ref_put(v___y_1620_, v___x_1654_);
v___x_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1651_);
return v___x_1656_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___boxed(lean_object* v_declName_1663_, lean_object* v_s_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
uint8_t v_s_boxed_1668_; lean_object* v_res_1669_; 
v_s_boxed_1668_ = lean_unbox(v_s_1664_);
v_res_1669_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg(v_declName_1663_, v_s_boxed_1668_, v___y_1665_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec(v___y_1665_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16(lean_object* v_declName_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
uint8_t v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = 0;
v___x_1677_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg(v_declName_1670_, v___x_1676_, v___y_1672_, v___y_1674_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16___boxed(lean_object* v_declName_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16(v_declName_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
return v_res_1684_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__18(lean_object* v_a_1685_, lean_object* v_x_1686_){
_start:
{
if (lean_obj_tag(v_x_1686_) == 0)
{
uint8_t v___x_1687_; 
v___x_1687_ = 0;
return v___x_1687_;
}
else
{
lean_object* v_head_1688_; lean_object* v_tail_1689_; uint8_t v___x_1690_; 
v_head_1688_ = lean_ctor_get(v_x_1686_, 0);
v_tail_1689_ = lean_ctor_get(v_x_1686_, 1);
v___x_1690_ = lean_name_eq(v_a_1685_, v_head_1688_);
if (v___x_1690_ == 0)
{
v_x_1686_ = v_tail_1689_;
goto _start;
}
else
{
return v___x_1690_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__18___boxed(lean_object* v_a_1692_, lean_object* v_x_1693_){
_start:
{
uint8_t v_res_1694_; lean_object* v_r_1695_; 
v_res_1694_ = l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__18(v_a_1692_, v_x_1693_);
lean_dec(v_x_1693_);
lean_dec(v_a_1692_);
v_r_1695_ = lean_box(v_res_1694_);
return v_r_1695_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__1(void){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__0));
v___x_1698_ = l_Lean_stringToMessageData(v___x_1697_);
return v___x_1698_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__3(void){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__2));
v___x_1701_ = l_Lean_stringToMessageData(v___x_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19(lean_object* v_a_1702_, lean_object* v_indName_1703_, lean_object* v_as_1704_, size_t v_sz_1705_, size_t v_i_1706_, lean_object* v_b_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v_a_1714_; uint8_t v___x_1718_; 
v___x_1718_ = lean_usize_dec_lt(v_i_1706_, v_sz_1705_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; 
lean_dec(v_indName_1703_);
v___x_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1719_, 0, v_b_1707_);
return v___x_1719_;
}
else
{
lean_object* v_ctors_1720_; lean_object* v___x_1721_; lean_object* v_a_1722_; uint8_t v___x_1723_; 
v_ctors_1720_ = lean_ctor_get(v_a_1702_, 4);
v___x_1721_ = lean_box(0);
v_a_1722_ = lean_array_uget_borrowed(v_as_1704_, v_i_1706_);
v___x_1723_ = l_List_elem___at___00Lean_Meta_mkSparseCasesOn_spec__18(v_a_1722_, v_ctors_1720_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1724_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__1);
lean_inc(v_a_1722_);
v___x_1725_ = l_Lean_MessageData_ofName(v_a_1722_);
v___x_1726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1724_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
v___x_1727_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___closed__3);
v___x_1728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1726_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
lean_inc(v_indName_1703_);
v___x_1729_ = l_Lean_MessageData_ofName(v_indName_1703_);
v___x_1730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1728_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
v___x_1731_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___x_1730_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_dec_ref_known(v___x_1731_, 1);
v_a_1714_ = v___x_1721_;
goto v___jp_1713_;
}
else
{
lean_dec(v_indName_1703_);
return v___x_1731_;
}
}
else
{
v_a_1714_ = v___x_1721_;
goto v___jp_1713_;
}
}
v___jp_1713_:
{
size_t v___x_1715_; size_t v___x_1716_; 
v___x_1715_ = ((size_t)1ULL);
v___x_1716_ = lean_usize_add(v_i_1706_, v___x_1715_);
v_i_1706_ = v___x_1716_;
v_b_1707_ = v_a_1714_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19___boxed(lean_object* v_a_1732_, lean_object* v_indName_1733_, lean_object* v_as_1734_, lean_object* v_sz_1735_, lean_object* v_i_1736_, lean_object* v_b_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
size_t v_sz_boxed_1743_; size_t v_i_boxed_1744_; lean_object* v_res_1745_; 
v_sz_boxed_1743_ = lean_unbox_usize(v_sz_1735_);
lean_dec(v_sz_1735_);
v_i_boxed_1744_ = lean_unbox_usize(v_i_1736_);
lean_dec(v_i_1736_);
v_res_1745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19(v_a_1732_, v_indName_1733_, v_as_1734_, v_sz_boxed_1743_, v_i_boxed_1744_, v_b_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec_ref(v_as_1734_);
lean_dec_ref(v_a_1732_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_mkSparseCasesOn_spec__7(lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
if (lean_obj_tag(v_a_1746_) == 0)
{
lean_object* v___x_1748_; 
v___x_1748_ = l_List_reverse___redArg(v_a_1747_);
return v___x_1748_;
}
else
{
lean_object* v_head_1749_; lean_object* v_tail_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1759_; 
v_head_1749_ = lean_ctor_get(v_a_1746_, 0);
v_tail_1750_ = lean_ctor_get(v_a_1746_, 1);
v_isSharedCheck_1759_ = !lean_is_exclusive(v_a_1746_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1752_ = v_a_1746_;
v_isShared_1753_ = v_isSharedCheck_1759_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_tail_1750_);
lean_inc(v_head_1749_);
lean_dec(v_a_1746_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1759_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1754_; lean_object* v___x_1756_; 
v___x_1754_ = l_Lean_mkLevelParam(v_head_1749_);
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 1, v_a_1747_);
lean_ctor_set(v___x_1752_, 0, v___x_1754_);
v___x_1756_ = v___x_1752_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1754_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_a_1747_);
v___x_1756_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
v_a_1746_ = v_tail_1750_;
v_a_1747_ = v___x_1756_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__0));
v___x_1762_ = l_Lean_stringToMessageData(v___x_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5(lean_object* v_constName_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; lean_object* v_env_1770_; lean_object* v___x_1771_; 
v___x_1769_ = lean_st_ref_get(v___y_1767_);
v_env_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc_ref(v_env_1770_);
lean_dec(v___x_1769_);
lean_inc(v_constName_1763_);
v___x_1771_ = l_Lean_isInductiveCore_x3f(v_env_1770_, v_constName_1763_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v___x_1772_; uint8_t v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1772_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0);
v___x_1773_ = 0;
v___x_1774_ = l_Lean_MessageData_ofConstName(v_constName_1763_, v___x_1773_);
v___x_1775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1772_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___closed__1);
v___x_1777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1775_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___x_1777_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
return v___x_1778_;
}
else
{
lean_object* v_val_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec(v_constName_1763_);
v_val_1779_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1771_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_val_1779_);
lean_dec(v___x_1771_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set_tag(v___x_1781_, 0);
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_val_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5___boxed(lean_object* v_constName_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5(v_constName_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
return v_res_1793_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__0(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1794_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__5));
v___x_1795_ = lean_unsigned_to_nat(42u);
v___x_1796_ = lean_unsigned_to_nat(82u);
v___x_1797_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__1));
v___x_1798_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___lam__0___closed__0));
v___x_1799_ = l_mkPanicMessageWithDecl(v___x_1798_, v___x_1797_, v___x_1796_, v___x_1795_, v___x_1794_);
return v___x_1799_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__2(void){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__1));
v___x_1802_ = l_Lean_stringToMessageData(v___x_1801_);
return v___x_1802_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__3(void){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_1803_;
}
}
static lean_object* _init_l_Lean_Meta_mkSparseCasesOn___closed__7(void){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__6));
v___x_1809_ = l_Lean_stringToMessageData(v___x_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn(lean_object* v_indName_1810_, lean_object* v_ctors_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v___x_1817_; lean_object* v___y_1819_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; uint8_t v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; uint8_t v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; uint8_t v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; uint8_t v___y_2025_; lean_object* v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v_env_2072_; uint8_t v___y_2074_; lean_object* v___x_2130_; uint8_t v_isModule_2131_; 
v___x_1817_ = l_Lean_instInhabitedExpr;
v___x_2070_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__3, &l_Lean_Meta_mkSparseCasesOn___closed__3_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__3);
v___x_2071_ = lean_st_ref_get(v_a_1815_);
v_env_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc_ref(v_env_2072_);
lean_dec(v___x_2071_);
v___x_2130_ = l_Lean_Environment_header(v_env_2072_);
v_isModule_2131_ = lean_ctor_get_uint8(v___x_2130_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_2130_);
if (v_isModule_2131_ == 0)
{
v___y_2074_ = v_isModule_2131_;
goto v___jp_2073_;
}
else
{
uint8_t v_isExporting_2132_; 
v_isExporting_2132_ = lean_ctor_get_uint8(v_env_2072_, sizeof(void*)*13);
if (v_isExporting_2132_ == 0)
{
v___y_2074_ = v_isModule_2131_;
goto v___jp_2073_;
}
else
{
uint8_t v___x_2133_; 
v___x_2133_ = 0;
v___y_2074_ = v___x_2133_;
goto v___jp_2073_;
}
}
v___jp_1818_:
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Lean_ConstantInfo_levelParams(v___y_1827_);
if (lean_obj_tag(v___x_1838_) == 1)
{
lean_object* v_tail_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___f_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v_tail_1839_ = lean_ctor_get(v___x_1838_, 1);
v___x_1840_ = lean_box(0);
lean_inc(v_tail_1839_);
v___x_1841_ = l_List_mapTR_loop___at___00Lean_Meta_mkSparseCasesOn_spec__7(v_tail_1839_, v___x_1840_);
v___x_1842_ = lean_box(v___y_1824_);
lean_inc_ref(v_ctors_1811_);
v___f_1843_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSparseCasesOn___lam__2___boxed), 17, 10);
lean_closure_set(v___f_1843_, 0, v___y_1825_);
lean_closure_set(v___f_1843_, 1, v___x_1817_);
lean_closure_set(v___f_1843_, 2, v___y_1821_);
lean_closure_set(v___f_1843_, 3, v___x_1842_);
lean_closure_set(v___f_1843_, 4, v_ctors_1811_);
lean_closure_set(v___f_1843_, 5, v___y_1823_);
lean_closure_set(v___f_1843_, 6, v___x_1841_);
lean_closure_set(v___f_1843_, 7, v___y_1819_);
lean_closure_set(v___f_1843_, 8, v___y_1822_);
lean_closure_set(v___f_1843_, 9, v___y_1820_);
v___x_1844_ = l_Lean_ConstantInfo_type(v___y_1827_);
lean_dec_ref(v___y_1827_);
v___x_1845_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_mkSparseCasesOn_spec__12___redArg(v___x_1844_, v___f_1843_, v___y_1831_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1847_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc_n(v_a_1846_, 2);
lean_dec_ref_known(v___x_1845_, 1);
lean_inc(v___y_1837_);
lean_inc_ref(v___y_1836_);
lean_inc(v___y_1835_);
lean_inc_ref(v___y_1834_);
v___x_1847_ = lean_infer_type(v_a_1846_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_2001_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref_known(v___x_1847_, 1);
v___x_1849_ = lean_box(1);
lean_inc(v___y_1830_);
v___x_1850_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_Meta_mkSparseCasesOn_spec__15___redArg(v___y_1830_, v___x_1838_, v_a_1848_, v_a_1846_, v___x_1849_, v___y_1837_);
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1853_ = v___x_1850_;
v_isShared_1854_ = v_isSharedCheck_2001_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1850_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_2001_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
lean_ctor_set_tag(v___x_1853_, 1);
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Lean_addDecl(v___x_1856_, v___y_1831_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v___x_1858_; lean_object* v_env_1859_; lean_object* v_nextMacroScope_1860_; lean_object* v_ngen_1861_; lean_object* v_auxDeclNGen_1862_; lean_object* v_traceState_1863_; lean_object* v_recordedDeps_1864_; lean_object* v_messages_1865_; lean_object* v_infoState_1866_; lean_object* v_snapshotTasks_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1990_; 
lean_dec_ref_known(v___x_1857_, 1);
v___x_1858_ = lean_st_ref_take(v___y_1837_);
v_env_1859_ = lean_ctor_get(v___x_1858_, 0);
v_nextMacroScope_1860_ = lean_ctor_get(v___x_1858_, 1);
v_ngen_1861_ = lean_ctor_get(v___x_1858_, 2);
v_auxDeclNGen_1862_ = lean_ctor_get(v___x_1858_, 3);
v_traceState_1863_ = lean_ctor_get(v___x_1858_, 4);
v_recordedDeps_1864_ = lean_ctor_get(v___x_1858_, 6);
v_messages_1865_ = lean_ctor_get(v___x_1858_, 7);
v_infoState_1866_ = lean_ctor_get(v___x_1858_, 8);
v_snapshotTasks_1867_ = lean_ctor_get(v___x_1858_, 9);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1990_ == 0)
{
lean_object* v_unused_1991_; 
v_unused_1991_ = lean_ctor_get(v___x_1858_, 5);
lean_dec(v_unused_1991_);
v___x_1869_ = v___x_1858_;
v_isShared_1870_ = v_isSharedCheck_1990_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_snapshotTasks_1867_);
lean_inc(v_infoState_1866_);
lean_inc(v_messages_1865_);
lean_inc(v_recordedDeps_1864_);
lean_inc(v_traceState_1863_);
lean_inc(v_auxDeclNGen_1862_);
lean_inc(v_ngen_1861_);
lean_inc(v_nextMacroScope_1860_);
lean_inc(v_env_1859_);
lean_dec(v___x_1858_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1990_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
uint8_t v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1875_; 
v___x_1871_ = 1;
lean_inc_ref(v___y_1826_);
v___x_1872_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___y_1826_, v_env_1859_, v___y_1833_, v___y_1828_, v___y_1829_, v___x_1871_);
v___x_1873_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__1);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 5, v___x_1873_);
lean_ctor_set(v___x_1869_, 0, v___x_1872_);
v___x_1875_ = v___x_1869_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1872_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_nextMacroScope_1860_);
lean_ctor_set(v_reuseFailAlloc_1989_, 2, v_ngen_1861_);
lean_ctor_set(v_reuseFailAlloc_1989_, 3, v_auxDeclNGen_1862_);
lean_ctor_set(v_reuseFailAlloc_1989_, 4, v_traceState_1863_);
lean_ctor_set(v_reuseFailAlloc_1989_, 5, v___x_1873_);
lean_ctor_set(v_reuseFailAlloc_1989_, 6, v_recordedDeps_1864_);
lean_ctor_set(v_reuseFailAlloc_1989_, 7, v_messages_1865_);
lean_ctor_set(v_reuseFailAlloc_1989_, 8, v_infoState_1866_);
lean_ctor_set(v_reuseFailAlloc_1989_, 9, v_snapshotTasks_1867_);
v___x_1875_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v_mctx_1878_; lean_object* v_zetaDeltaFVarIds_1879_; lean_object* v_postponed_1880_; lean_object* v_diag_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1987_; 
v___x_1876_ = lean_st_ref_put(v___y_1837_, v___x_1875_);
v___x_1877_ = lean_st_ref_take(v___y_1835_);
v_mctx_1878_ = lean_ctor_get(v___x_1877_, 0);
v_zetaDeltaFVarIds_1879_ = lean_ctor_get(v___x_1877_, 2);
v_postponed_1880_ = lean_ctor_get(v___x_1877_, 3);
v_diag_1881_ = lean_ctor_get(v___x_1877_, 4);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1987_ == 0)
{
lean_object* v_unused_1988_; 
v_unused_1988_ = lean_ctor_get(v___x_1877_, 1);
lean_dec(v_unused_1988_);
v___x_1883_ = v___x_1877_;
v_isShared_1884_ = v_isSharedCheck_1987_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_diag_1881_);
lean_inc(v_postponed_1880_);
lean_inc(v_zetaDeltaFVarIds_1879_);
lean_inc(v_mctx_1878_);
lean_dec(v___x_1877_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1987_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1885_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg___closed__2);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 1, v___x_1885_);
v___x_1887_ = v___x_1883_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_mctx_1878_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1986_, 2, v_zetaDeltaFVarIds_1879_);
lean_ctor_set(v_reuseFailAlloc_1986_, 3, v_postponed_1880_);
lean_ctor_set(v_reuseFailAlloc_1986_, 4, v_diag_1881_);
v___x_1887_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v_env_1891_; lean_object* v_nextMacroScope_1892_; lean_object* v_ngen_1893_; lean_object* v_auxDeclNGen_1894_; lean_object* v_traceState_1895_; lean_object* v_recordedDeps_1896_; lean_object* v_messages_1897_; lean_object* v_infoState_1898_; lean_object* v_snapshotTasks_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1984_; 
v___x_1888_ = lean_st_ref_put(v___y_1835_, v___x_1887_);
lean_inc(v___y_1830_);
v___x_1889_ = l_Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16(v___y_1830_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
lean_dec_ref(v___x_1889_);
v___x_1890_ = lean_st_ref_take(v___y_1837_);
v_env_1891_ = lean_ctor_get(v___x_1890_, 0);
v_nextMacroScope_1892_ = lean_ctor_get(v___x_1890_, 1);
v_ngen_1893_ = lean_ctor_get(v___x_1890_, 2);
v_auxDeclNGen_1894_ = lean_ctor_get(v___x_1890_, 3);
v_traceState_1895_ = lean_ctor_get(v___x_1890_, 4);
v_recordedDeps_1896_ = lean_ctor_get(v___x_1890_, 6);
v_messages_1897_ = lean_ctor_get(v___x_1890_, 7);
v_infoState_1898_ = lean_ctor_get(v___x_1890_, 8);
v_snapshotTasks_1899_ = lean_ctor_get(v___x_1890_, 9);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1984_ == 0)
{
lean_object* v_unused_1985_; 
v_unused_1985_ = lean_ctor_get(v___x_1890_, 5);
lean_dec(v_unused_1985_);
v___x_1901_ = v___x_1890_;
v_isShared_1902_ = v_isSharedCheck_1984_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_snapshotTasks_1899_);
lean_inc(v_infoState_1898_);
lean_inc(v_messages_1897_);
lean_inc(v_recordedDeps_1896_);
lean_inc(v_traceState_1895_);
lean_inc(v_auxDeclNGen_1894_);
lean_inc(v_ngen_1893_);
lean_inc(v_nextMacroScope_1892_);
lean_inc(v_env_1891_);
lean_dec(v___x_1890_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1984_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1903_; lean_object* v___x_1905_; 
lean_inc(v___y_1830_);
v___x_1903_ = l_Lean_markSparseCasesOn(v_env_1891_, v___y_1830_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 5, v___x_1873_);
lean_ctor_set(v___x_1901_, 0, v___x_1903_);
v___x_1905_ = v___x_1901_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1903_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_nextMacroScope_1892_);
lean_ctor_set(v_reuseFailAlloc_1983_, 2, v_ngen_1893_);
lean_ctor_set(v_reuseFailAlloc_1983_, 3, v_auxDeclNGen_1894_);
lean_ctor_set(v_reuseFailAlloc_1983_, 4, v_traceState_1895_);
lean_ctor_set(v_reuseFailAlloc_1983_, 5, v___x_1873_);
lean_ctor_set(v_reuseFailAlloc_1983_, 6, v_recordedDeps_1896_);
lean_ctor_set(v_reuseFailAlloc_1983_, 7, v_messages_1897_);
lean_ctor_set(v_reuseFailAlloc_1983_, 8, v_infoState_1898_);
lean_ctor_set(v_reuseFailAlloc_1983_, 9, v_snapshotTasks_1899_);
v___x_1905_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v_mctx_1908_; lean_object* v_zetaDeltaFVarIds_1909_; lean_object* v_postponed_1910_; lean_object* v_diag_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1981_; 
v___x_1906_ = lean_st_ref_put(v___y_1837_, v___x_1905_);
v___x_1907_ = lean_st_ref_take(v___y_1835_);
v_mctx_1908_ = lean_ctor_get(v___x_1907_, 0);
v_zetaDeltaFVarIds_1909_ = lean_ctor_get(v___x_1907_, 2);
v_postponed_1910_ = lean_ctor_get(v___x_1907_, 3);
v_diag_1911_ = lean_ctor_get(v___x_1907_, 4);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1981_ == 0)
{
lean_object* v_unused_1982_; 
v_unused_1982_ = lean_ctor_get(v___x_1907_, 1);
lean_dec(v_unused_1982_);
v___x_1913_ = v___x_1907_;
v_isShared_1914_ = v_isSharedCheck_1981_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_diag_1911_);
lean_inc(v_postponed_1910_);
lean_inc(v_zetaDeltaFVarIds_1909_);
lean_inc(v_mctx_1908_);
lean_dec(v___x_1907_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1981_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 1, v___x_1885_);
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_mctx_1908_);
lean_ctor_set(v_reuseFailAlloc_1980_, 1, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1980_, 2, v_zetaDeltaFVarIds_1909_);
lean_ctor_set(v_reuseFailAlloc_1980_, 3, v_postponed_1910_);
lean_ctor_set(v_reuseFailAlloc_1980_, 4, v_diag_1911_);
v___x_1916_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v_env_1919_; lean_object* v_nextMacroScope_1920_; lean_object* v_ngen_1921_; lean_object* v_auxDeclNGen_1922_; lean_object* v_traceState_1923_; lean_object* v_recordedDeps_1924_; lean_object* v_messages_1925_; lean_object* v_infoState_1926_; lean_object* v_snapshotTasks_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1978_; 
v___x_1917_ = lean_st_ref_put(v___y_1835_, v___x_1916_);
v___x_1918_ = lean_st_ref_take(v___y_1837_);
v_env_1919_ = lean_ctor_get(v___x_1918_, 0);
v_nextMacroScope_1920_ = lean_ctor_get(v___x_1918_, 1);
v_ngen_1921_ = lean_ctor_get(v___x_1918_, 2);
v_auxDeclNGen_1922_ = lean_ctor_get(v___x_1918_, 3);
v_traceState_1923_ = lean_ctor_get(v___x_1918_, 4);
v_recordedDeps_1924_ = lean_ctor_get(v___x_1918_, 6);
v_messages_1925_ = lean_ctor_get(v___x_1918_, 7);
v_infoState_1926_ = lean_ctor_get(v___x_1918_, 8);
v_snapshotTasks_1927_ = lean_ctor_get(v___x_1918_, 9);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1978_ == 0)
{
lean_object* v_unused_1979_; 
v_unused_1979_ = lean_ctor_get(v___x_1918_, 5);
lean_dec(v_unused_1979_);
v___x_1929_ = v___x_1918_;
v_isShared_1930_ = v_isSharedCheck_1978_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_snapshotTasks_1927_);
lean_inc(v_infoState_1926_);
lean_inc(v_messages_1925_);
lean_inc(v_recordedDeps_1924_);
lean_inc(v_traceState_1923_);
lean_inc(v_auxDeclNGen_1922_);
lean_inc(v_ngen_1921_);
lean_inc(v_nextMacroScope_1920_);
lean_inc(v_env_1919_);
lean_dec(v___x_1918_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1978_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v_numParams_1931_; lean_object* v_numIndices_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1944_; 
v_numParams_1931_ = lean_ctor_get(v___y_1832_, 1);
lean_inc(v_numParams_1931_);
v_numIndices_1932_ = lean_ctor_get(v___y_1832_, 2);
lean_inc(v_numIndices_1932_);
lean_dec_ref(v___y_1832_);
v___x_1933_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
v___x_1934_ = lean_unsigned_to_nat(1u);
v___x_1935_ = lean_nat_add(v_numParams_1931_, v___x_1934_);
lean_dec(v_numParams_1931_);
v___x_1936_ = lean_nat_add(v___x_1935_, v_numIndices_1932_);
lean_dec(v_numIndices_1932_);
lean_dec(v___x_1935_);
v___x_1937_ = lean_nat_add(v___x_1936_, v___x_1934_);
v___x_1938_ = lean_array_get_size(v_ctors_1811_);
v___x_1939_ = lean_nat_add(v___x_1937_, v___x_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_nat_add(v___x_1939_, v___x_1934_);
lean_dec(v___x_1939_);
v___x_1941_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1941_, 0, v_indName_1810_);
lean_ctor_set(v___x_1941_, 1, v___x_1936_);
lean_ctor_set(v___x_1941_, 2, v___x_1940_);
lean_ctor_set(v___x_1941_, 3, v_ctors_1811_);
lean_inc(v___y_1830_);
v___x_1942_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1933_, v_env_1919_, v___y_1830_, v___x_1941_, v___y_1831_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 5, v___x_1873_);
lean_ctor_set(v___x_1929_, 0, v___x_1942_);
v___x_1944_ = v___x_1929_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1942_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_nextMacroScope_1920_);
lean_ctor_set(v_reuseFailAlloc_1977_, 2, v_ngen_1921_);
lean_ctor_set(v_reuseFailAlloc_1977_, 3, v_auxDeclNGen_1922_);
lean_ctor_set(v_reuseFailAlloc_1977_, 4, v_traceState_1923_);
lean_ctor_set(v_reuseFailAlloc_1977_, 5, v___x_1873_);
lean_ctor_set(v_reuseFailAlloc_1977_, 6, v_recordedDeps_1924_);
lean_ctor_set(v_reuseFailAlloc_1977_, 7, v_messages_1925_);
lean_ctor_set(v_reuseFailAlloc_1977_, 8, v_infoState_1926_);
lean_ctor_set(v_reuseFailAlloc_1977_, 9, v_snapshotTasks_1927_);
v___x_1944_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v_mctx_1947_; lean_object* v_zetaDeltaFVarIds_1948_; lean_object* v_postponed_1949_; lean_object* v_diag_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1975_; 
v___x_1945_ = lean_st_ref_put(v___y_1837_, v___x_1944_);
v___x_1946_ = lean_st_ref_take(v___y_1835_);
v_mctx_1947_ = lean_ctor_get(v___x_1946_, 0);
v_zetaDeltaFVarIds_1948_ = lean_ctor_get(v___x_1946_, 2);
v_postponed_1949_ = lean_ctor_get(v___x_1946_, 3);
v_diag_1950_ = lean_ctor_get(v___x_1946_, 4);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1975_ == 0)
{
lean_object* v_unused_1976_; 
v_unused_1976_ = lean_ctor_get(v___x_1946_, 1);
lean_dec(v_unused_1976_);
v___x_1952_ = v___x_1946_;
v_isShared_1953_ = v_isSharedCheck_1975_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_diag_1950_);
lean_inc(v_postponed_1949_);
lean_inc(v_zetaDeltaFVarIds_1948_);
lean_inc(v_mctx_1947_);
lean_dec(v___x_1946_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1975_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 1, v___x_1885_);
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_mctx_1947_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1974_, 2, v_zetaDeltaFVarIds_1948_);
lean_ctor_set(v_reuseFailAlloc_1974_, 3, v_postponed_1949_);
lean_ctor_set(v_reuseFailAlloc_1974_, 4, v_diag_1950_);
v___x_1955_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = lean_st_ref_put(v___y_1835_, v___x_1955_);
lean_inc(v___y_1830_);
v___x_1957_ = l_Lean_enableRealizationsForConst(v___y_1830_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1964_ == 0)
{
lean_object* v_unused_1965_; 
v_unused_1965_ = lean_ctor_get(v___x_1957_, 0);
lean_dec(v_unused_1965_);
v___x_1959_ = v___x_1957_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_dec(v___x_1957_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___y_1830_);
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___y_1830_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec(v___y_1830_);
v_a_1966_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1957_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1957_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
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
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec_ref(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v_ctors_1811_);
lean_dec(v_indName_1810_);
v_a_1992_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1857_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1857_);
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
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
lean_dec(v_a_1846_);
lean_dec_ref_known(v___x_1838_, 2);
lean_dec_ref(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v_ctors_1811_);
lean_dec(v_indName_1810_);
v_a_2002_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1847_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1847_);
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
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
lean_dec_ref_known(v___x_1838_, 2);
lean_dec_ref(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v_ctors_1811_);
lean_dec(v_indName_1810_);
v_a_2010_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_1845_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_1845_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
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
lean_object* v___x_2018_; lean_object* v___x_2019_; 
lean_dec(v___x_1838_);
lean_dec_ref(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v___y_1830_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1825_);
lean_dec(v___y_1823_);
lean_dec(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec_ref(v_ctors_1811_);
lean_dec(v_indName_1810_);
v___x_2018_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__0, &l_Lean_Meta_mkSparseCasesOn___closed__0_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__0);
v___x_2019_ = l_panic___at___00Lean_Meta_mkSparseCasesOn_spec__17(v___x_2018_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
return v___x_2019_;
}
}
v___jp_2020_:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
lean_inc(v_indName_1810_);
v___x_2033_ = l_Lean_mkCasesOnName(v_indName_1810_);
lean_inc(v___x_2033_);
v___x_2034_ = l_Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6(v___x_2033_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_toConstantVal_2035_; lean_object* v_a_2036_; lean_object* v_numParams_2037_; lean_object* v_numIndices_2038_; lean_object* v_ctors_2039_; lean_object* v_levelParams_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; uint8_t v___x_2047_; 
v_toConstantVal_2035_ = lean_ctor_get(v___y_2022_, 0);
v_a_2036_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2036_);
lean_dec_ref_known(v___x_2034_, 1);
v_numParams_2037_ = lean_ctor_get(v___y_2022_, 1);
lean_inc(v_numParams_2037_);
v_numIndices_2038_ = lean_ctor_get(v___y_2022_, 2);
lean_inc(v_numIndices_2038_);
v_ctors_2039_ = lean_ctor_get(v___y_2022_, 4);
lean_inc(v_ctors_2039_);
v_levelParams_2040_ = lean_ctor_get(v_toConstantVal_2035_, 1);
lean_inc(v_indName_1810_);
v___x_2041_ = l_Lean_mkCtorIdxName(v_indName_1810_);
v___x_2042_ = l_Lean_ConstantInfo_levelParams(v_a_2036_);
v___x_2043_ = l_List_lengthTR___redArg(v___x_2042_);
lean_dec(v___x_2042_);
v___x_2044_ = l_List_lengthTR___redArg(v_levelParams_2040_);
v___x_2045_ = lean_unsigned_to_nat(1u);
v___x_2046_ = lean_nat_add(v___x_2044_, v___x_2045_);
lean_dec(v___x_2044_);
v___x_2047_ = lean_nat_dec_eq(v___x_2043_, v___x_2046_);
lean_dec(v___x_2046_);
lean_dec(v___x_2043_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_dec(v___x_2041_);
lean_dec(v_ctors_2039_);
lean_dec(v_numIndices_2038_);
lean_dec(v_numParams_2037_);
lean_dec(v_a_2036_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2022_);
lean_dec_ref(v_ctors_1811_);
lean_dec(v_indName_1810_);
v___x_2048_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__2, &l_Lean_Meta_mkSparseCasesOn___closed__2_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__2);
v___x_2049_ = l_Lean_MessageData_ofConstName(v___x_2033_, v___x_2047_);
v___x_2050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2048_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
v___x_2051_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0, &l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Meta_mkSparseCasesOn_spec__0___closed__0);
v___x_2052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2050_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
v___x_2053_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___x_2052_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2053_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2053_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
else
{
lean_inc(v_a_2036_);
v___y_1819_ = v_a_2036_;
v___y_1820_ = v___x_2033_;
v___y_1821_ = v_numIndices_2038_;
v___y_1822_ = v_ctors_2039_;
v___y_1823_ = v___x_2041_;
v___y_1824_ = v___y_2021_;
v___y_1825_ = v_numParams_2037_;
v___y_1826_ = v___y_2023_;
v___y_1827_ = v_a_2036_;
v___y_1828_ = v___y_2024_;
v___y_1829_ = v___y_2027_;
v___y_1830_ = v___y_2026_;
v___y_1831_ = v___y_2025_;
v___y_1832_ = v___y_2022_;
v___y_1833_ = v___y_2028_;
v___y_1834_ = v___y_2029_;
v___y_1835_ = v___y_2030_;
v___y_1836_ = v___y_2031_;
v___y_1837_ = v___y_2032_;
goto v___jp_1818_;
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec(v___x_2033_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2022_);
lean_dec_ref(v_ctors_1811_);
lean_dec(v_indName_1810_);
v_a_2062_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2034_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2034_);
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
v___jp_2073_:
{
lean_object* v___x_2075_; lean_object* v_asyncMode_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2075_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt;
v_asyncMode_2076_ = lean_ctor_get(v___x_2075_, 2);
lean_inc_ref(v_ctors_1811_);
lean_inc(v_indName_1810_);
v___x_2077_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2077_, 0, v_indName_1810_);
lean_ctor_set(v___x_2077_, 1, v_ctors_1811_);
lean_ctor_set_uint8(v___x_2077_, sizeof(void*)*2, v___y_2074_);
v___x_2078_ = lean_box(0);
v___x_2079_ = 0;
v___x_2080_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2070_, v___x_2075_, v_env_2072_, v_asyncMode_2076_, v___x_2078_, v___x_2079_);
v___x_2081_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v___x_2080_, v___x_2077_);
lean_dec(v___x_2080_);
if (lean_obj_tag(v___x_2081_) == 1)
{
lean_object* v_val_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
lean_dec_ref_known(v___x_2077_, 2);
lean_dec_ref(v_ctors_1811_);
lean_dec(v_indName_1810_);
v_val_2082_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2081_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_val_2082_);
lean_dec(v___x_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
lean_ctor_set_tag(v___x_2084_, 0);
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_val_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
else
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v_a_2092_; lean_object* v___f_2093_; lean_object* v___x_2094_; 
lean_dec(v___x_2081_);
v___x_2090_ = ((lean_object*)(l_Lean_Meta_mkSparseCasesOn___closed__5));
v___x_2091_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_mkSparseCasesOn_spec__2___redArg(v___x_2090_, v_a_1815_);
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc_n(v_a_2092_, 2);
lean_dec_ref(v___x_2091_);
v___f_2093_ = lean_alloc_closure((void*)(l_Lean_Meta_mkSparseCasesOn___lam__0), 3, 2);
lean_closure_set(v___f_2093_, 0, v___x_2077_);
lean_closure_set(v___f_2093_, 1, v_a_2092_);
lean_inc(v_indName_1810_);
v___x_2094_ = l_Lean_getConstInfoInduct___at___00Lean_Meta_mkSparseCasesOn_spec__5(v_indName_1810_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2096_; size_t v_sz_2097_; size_t v___x_2098_; lean_object* v___x_2099_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2096_ = lean_box(0);
v_sz_2097_ = lean_array_size(v_ctors_1811_);
v___x_2098_ = ((size_t)0ULL);
lean_inc(v_indName_1810_);
v___x_2099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkSparseCasesOn_spec__19(v_a_2095_, v_indName_1810_, v_ctors_1811_, v_sz_2097_, v___x_2098_, v___x_2096_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_ctors_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; 
lean_dec_ref_known(v___x_2099_, 1);
v_ctors_2100_ = lean_ctor_get(v_a_2095_, 4);
v___x_2101_ = lean_array_get_size(v_ctors_1811_);
v___x_2102_ = l_List_lengthTR___redArg(v_ctors_2100_);
v___x_2103_ = lean_nat_dec_eq(v___x_2101_, v___x_2102_);
lean_dec(v___x_2102_);
if (v___x_2103_ == 0)
{
v___y_2021_ = v___x_2079_;
v___y_2022_ = v_a_2095_;
v___y_2023_ = v___x_2075_;
v___y_2024_ = v_asyncMode_2076_;
v___y_2025_ = v___x_2079_;
v___y_2026_ = v_a_2092_;
v___y_2027_ = v___x_2078_;
v___y_2028_ = v___f_2093_;
v___y_2029_ = v_a_1812_;
v___y_2030_ = v_a_1813_;
v___y_2031_ = v_a_1814_;
v___y_2032_ = v_a_1815_;
goto v___jp_2020_;
}
else
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec(v_a_2095_);
lean_dec_ref(v___f_2093_);
lean_dec(v_a_2092_);
lean_dec_ref(v_ctors_1811_);
lean_dec(v_indName_1810_);
v___x_2104_ = lean_obj_once(&l_Lean_Meta_mkSparseCasesOn___closed__7, &l_Lean_Meta_mkSparseCasesOn___closed__7_once, _init_l_Lean_Meta_mkSparseCasesOn___closed__7);
v___x_2105_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v___x_2104_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2105_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2105_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec(v_a_2095_);
lean_dec_ref(v___f_2093_);
lean_dec(v_a_2092_);
lean_dec_ref(v_ctors_1811_);
lean_dec(v_indName_1810_);
v_a_2114_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2099_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2099_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec_ref(v___f_2093_);
lean_dec(v_a_2092_);
lean_dec_ref(v_ctors_1811_);
lean_dec(v_indName_1810_);
v_a_2122_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2094_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2094_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSparseCasesOn___boxed(lean_object* v_indName_2134_, lean_object* v_ctors_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l_Lean_Meta_mkSparseCasesOn(v_indName_2134_, v_ctors_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_);
lean_dec(v_a_2139_);
lean_dec_ref(v_a_2138_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1(lean_object* v_00_u03b2_2142_, lean_object* v_x_2143_, lean_object* v_x_2144_){
_start:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___redArg(v_x_2143_, v_x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1___boxed(lean_object* v_00_u03b2_2146_, lean_object* v_x_2147_, lean_object* v_x_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1(v_00_u03b2_2146_, v_x_2147_, v_x_2148_);
lean_dec_ref(v_x_2148_);
lean_dec_ref(v_x_2147_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3(lean_object* v_00_u03b2_2150_, lean_object* v_x_2151_, lean_object* v_x_2152_, lean_object* v_x_2153_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3___redArg(v_x_2151_, v_x_2152_, v_x_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14(lean_object* v_00_u03b1_2155_, lean_object* v_name_2156_, uint8_t v_bi_2157_, lean_object* v_type_2158_, lean_object* v_k_2159_, uint8_t v_kind_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___redArg(v_name_2156_, v_bi_2157_, v_type_2158_, v_k_2159_, v_kind_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14___boxed(lean_object* v_00_u03b1_2167_, lean_object* v_name_2168_, lean_object* v_bi_2169_, lean_object* v_type_2170_, lean_object* v_k_2171_, lean_object* v_kind_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
uint8_t v_bi_boxed_2178_; uint8_t v_kind_boxed_2179_; lean_object* v_res_2180_; 
v_bi_boxed_2178_ = lean_unbox(v_bi_2169_);
v_kind_boxed_2179_ = lean_unbox(v_kind_2172_);
v_res_2180_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10_spec__14(v_00_u03b1_2167_, v_name_2168_, v_bi_boxed_2178_, v_type_2170_, v_k_2171_, v_kind_boxed_2179_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10(lean_object* v_00_u03b1_2181_, lean_object* v_name_2182_, lean_object* v_type_2183_, lean_object* v_k_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___redArg(v_name_2182_, v_type_2183_, v_k_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10___boxed(lean_object* v_00_u03b1_2191_, lean_object* v_name_2192_, lean_object* v_type_2193_, lean_object* v_k_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkSparseCasesOn_spec__10(v_00_u03b1_2191_, v_name_2192_, v_type_2193_, v_k_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14(lean_object* v_00_u03b1_2201_, lean_object* v_msg_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___redArg(v_msg_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14___boxed(lean_object* v_00_u03b1_2209_, lean_object* v_msg_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lean_throwError___at___00Lean_Meta_mkSparseCasesOn_spec__14(v_00_u03b1_2209_, v_msg_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23(lean_object* v_declName_2217_, uint8_t v_s_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___redArg(v_declName_2217_, v_s_2218_, v___y_2220_, v___y_2222_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23___boxed(lean_object* v_declName_2225_, lean_object* v_s_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
uint8_t v_s_boxed_2232_; lean_object* v_res_2233_; 
v_s_boxed_2232_ = lean_unbox(v_s_2226_);
v_res_2233_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_Meta_mkSparseCasesOn_spec__16_spec__23(v_declName_2225_, v_s_boxed_2232_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(lean_object* v_00_u03b2_2234_, lean_object* v_x_2235_, size_t v_x_2236_, lean_object* v_x_2237_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___redArg(v_x_2235_, v_x_2236_, v_x_2237_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2239_, lean_object* v_x_2240_, lean_object* v_x_2241_, lean_object* v_x_2242_){
_start:
{
size_t v_x_24633__boxed_2243_; lean_object* v_res_2244_; 
v_x_24633__boxed_2243_ = lean_unbox_usize(v_x_2241_);
lean_dec(v_x_2241_);
v_res_2244_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2(v_00_u03b2_2239_, v_x_2240_, v_x_24633__boxed_2243_, v_x_2242_);
lean_dec_ref(v_x_2242_);
lean_dec_ref(v_x_2240_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(lean_object* v_00_u03b2_2245_, lean_object* v_x_2246_, size_t v_x_2247_, size_t v_x_2248_, lean_object* v_x_2249_, lean_object* v_x_2250_){
_start:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___redArg(v_x_2246_, v_x_2247_, v_x_2248_, v_x_2249_, v_x_2250_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5___boxed(lean_object* v_00_u03b2_2252_, lean_object* v_x_2253_, lean_object* v_x_2254_, lean_object* v_x_2255_, lean_object* v_x_2256_, lean_object* v_x_2257_){
_start:
{
size_t v_x_24644__boxed_2258_; size_t v_x_24645__boxed_2259_; lean_object* v_res_2260_; 
v_x_24644__boxed_2258_ = lean_unbox_usize(v_x_2254_);
lean_dec(v_x_2254_);
v_x_24645__boxed_2259_ = lean_unbox_usize(v_x_2255_);
lean_dec(v_x_2255_);
v_res_2260_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5(v_00_u03b2_2252_, v_x_2253_, v_x_24644__boxed_2258_, v_x_24645__boxed_2259_, v_x_2256_, v_x_2257_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9(lean_object* v_00_u03b1_2261_, lean_object* v_constName_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___redArg(v_constName_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9___boxed(lean_object* v_00_u03b1_2269_, lean_object* v_constName_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9(v_00_u03b1_2269_, v_constName_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8(lean_object* v_00_u03b2_2277_, lean_object* v_keys_2278_, lean_object* v_vals_2279_, lean_object* v_heq_2280_, lean_object* v_i_2281_, lean_object* v_k_2282_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___redArg(v_keys_2278_, v_vals_2279_, v_i_2281_, v_k_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8___boxed(lean_object* v_00_u03b2_2284_, lean_object* v_keys_2285_, lean_object* v_vals_2286_, lean_object* v_heq_2287_, lean_object* v_i_2288_, lean_object* v_k_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_mkSparseCasesOn_spec__1_spec__2_spec__8(v_00_u03b2_2284_, v_keys_2285_, v_vals_2286_, v_heq_2287_, v_i_2288_, v_k_2289_);
lean_dec_ref(v_k_2289_);
lean_dec_ref(v_vals_2286_);
lean_dec_ref(v_keys_2285_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11(lean_object* v_00_u03b2_2291_, lean_object* v_n_2292_, lean_object* v_k_2293_, lean_object* v_v_2294_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11___redArg(v_n_2292_, v_k_2293_, v_v_2294_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12(lean_object* v_00_u03b2_2296_, size_t v_depth_2297_, lean_object* v_keys_2298_, lean_object* v_vals_2299_, lean_object* v_heq_2300_, lean_object* v_i_2301_, lean_object* v_entries_2302_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___redArg(v_depth_2297_, v_keys_2298_, v_vals_2299_, v_i_2301_, v_entries_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12___boxed(lean_object* v_00_u03b2_2304_, lean_object* v_depth_2305_, lean_object* v_keys_2306_, lean_object* v_vals_2307_, lean_object* v_heq_2308_, lean_object* v_i_2309_, lean_object* v_entries_2310_){
_start:
{
size_t v_depth_boxed_2311_; lean_object* v_res_2312_; 
v_depth_boxed_2311_ = lean_unbox_usize(v_depth_2305_);
lean_dec(v_depth_2305_);
v_res_2312_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__12(v_00_u03b2_2304_, v_depth_boxed_2311_, v_keys_2306_, v_vals_2307_, v_heq_2308_, v_i_2309_, v_entries_2310_);
lean_dec_ref(v_vals_2307_);
lean_dec_ref(v_keys_2306_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16(lean_object* v_00_u03b1_2313_, lean_object* v_ref_2314_, lean_object* v_constName_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___redArg(v_ref_2314_, v_constName_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16___boxed(lean_object* v_00_u03b1_2322_, lean_object* v_ref_2323_, lean_object* v_constName_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16(v_00_u03b1_2322_, v_ref_2323_, v_constName_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v_ref_2323_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11_spec__27(lean_object* v_00_u03b2_2331_, lean_object* v_x_2332_, lean_object* v_x_2333_, lean_object* v_x_2334_, lean_object* v_x_2335_){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_mkSparseCasesOn_spec__3_spec__5_spec__11_spec__27___redArg(v_x_2332_, v_x_2333_, v_x_2334_, v_x_2335_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31(lean_object* v_00_u03b1_2337_, lean_object* v_ref_2338_, lean_object* v_msg_2339_, lean_object* v_declHint_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___redArg(v_ref_2338_, v_msg_2339_, v_declHint_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31___boxed(lean_object* v_00_u03b1_2347_, lean_object* v_ref_2348_, lean_object* v_msg_2349_, lean_object* v_declHint_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31(v_00_u03b1_2347_, v_ref_2348_, v_msg_2349_, v_declHint_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v_ref_2348_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35(lean_object* v_msg_2357_, lean_object* v_declHint_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___redArg(v_msg_2357_, v_declHint_2358_, v___y_2362_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35___boxed(lean_object* v_msg_2365_, lean_object* v_declHint_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__33_spec__35(v_msg_2365_, v_declHint_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34(lean_object* v_00_u03b1_2373_, lean_object* v_ref_2374_, lean_object* v_msg_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___redArg(v_ref_2374_, v_msg_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34___boxed(lean_object* v_00_u03b1_2382_, lean_object* v_ref_2383_, lean_object* v_msg_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_mkSparseCasesOn_spec__6_spec__9_spec__16_spec__31_spec__34(v_00_u03b1_2382_, v_ref_2383_, v_msg_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v_ref_2383_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfoCore(lean_object* v_env_2391_, lean_object* v_sparseCasesOnName_2392_){
_start:
{
lean_object* v___x_2393_; lean_object* v_toEnvExtension_2394_; lean_object* v_asyncMode_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; lean_object* v___x_2398_; 
v___x_2393_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
v_toEnvExtension_2394_ = lean_ctor_get(v___x_2393_, 0);
v_asyncMode_2395_ = lean_ctor_get(v_toEnvExtension_2394_, 2);
v___x_2396_ = ((lean_object*)(l_Lean_Meta_instInhabitedSparseCasesOnInfo_default));
v___x_2397_ = 0;
v___x_2398_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2396_, v___x_2393_, v_env_2391_, v_sparseCasesOnName_2392_, v_asyncMode_2395_, v___x_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg(lean_object* v_sparseCasesOnName_2399_, lean_object* v_a_2400_){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v_env_2404_; lean_object* v___x_2405_; lean_object* v_toEnvExtension_2406_; lean_object* v_asyncMode_2407_; uint8_t v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2402_ = ((lean_object*)(l_Lean_Meta_instInhabitedSparseCasesOnInfo_default));
v___x_2403_ = lean_st_ref_get(v_a_2400_);
v_env_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc_ref(v_env_2404_);
lean_dec(v___x_2403_);
v___x_2405_ = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt;
v_toEnvExtension_2406_ = lean_ctor_get(v___x_2405_, 0);
v_asyncMode_2407_ = lean_ctor_get(v_toEnvExtension_2406_, 2);
v___x_2408_ = 0;
v___x_2409_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_2402_, v___x_2405_, v_env_2404_, v_sparseCasesOnName_2399_, v_asyncMode_2407_, v___x_2408_);
v___x_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___redArg___boxed(lean_object* v_sparseCasesOnName_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_sparseCasesOnName_2411_, v_a_2412_);
lean_dec(v_a_2412_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo(lean_object* v_sparseCasesOnName_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = l_Lean_Meta_getSparseCasesOnInfo___redArg(v_sparseCasesOnName_2415_, v_a_2417_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSparseCasesOnInfo___boxed(lean_object* v_sparseCasesOnName_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l_Lean_Meta_getSparseCasesOnInfo(v_sparseCasesOnName_2420_, v_a_2421_, v_a_2422_);
lean_dec(v_a_2422_);
lean_dec_ref(v_a_2421_);
return v_res_2424_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_HasNotBit(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(uint8_t builtin) {
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
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_HasNotBit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_2982463813____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnCacheExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_initFn_00___x40_Lean_Meta_Constructions_SparseCasesOn_1625393638____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Constructions_SparseCasesOn_0__Lean_Meta_sparseCasesOnInfoExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Constructions_SparseCasesOn(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* initialize_Lean_Meta_HasNotBit(uint8_t builtin);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Constructions_SparseCasesOn(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_HasNotBit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Constructions_SparseCasesOn(builtin);
}
#ifdef __cplusplus
}
#endif
