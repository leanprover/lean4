// Lean compiler output
// Module: Lean.Compiler.LCNF.PhaseExt
// Imports: public import Lean.Compiler.LCNF.PassManager public import Lean.Compiler.LCNF.PublicDeclsExt
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instDecidableEqOLeanLevel(uint8_t, uint8_t);
uint8_t l_Lean_Compiler_LCNF_Phase_toPurity(uint8_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_Compiler_LCNF_isDeclPublic(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedDecl_default(uint8_t);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedSignature_default(uint8_t);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3496178540____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3496178540____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_baseTransparentDeclsExt;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1977385844____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1977385844____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_monoTransparentDeclsExt;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_975450157____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_975450157____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_impureTransparentDeclsExt;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_getTransparencyExt(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_getTransparencyExt___boxed(lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_isDeclTransparent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_isDeclTransparent___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_isDeclTransparent___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isDeclTransparent(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isDeclTransparent___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclTransparent___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclTransparent(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclTransparent___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__0_value;
static const lean_array_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "number of local entries: "};
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__1_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__3_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__4;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___boxed(lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__2_value;
static const lean_string_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__3_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4_value;
static const lean_array_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5_value;
static const lean_string_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__6_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7_value;
static const lean_string_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__8_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__9 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__9_value;
static const lean_string_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__10 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__10_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13;
static const lean_string_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__14 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__14_value;
static const lean_string_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__15 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__15_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16_value;
static const lean_string_object l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__17 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__17_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___auto__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_mkDeclExt___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__2___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_mkDeclExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_mkDeclExt___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_mkDeclExt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_mkDeclExt___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_mkDeclExt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_mkDeclExt___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_mkDeclExt___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___closed__3;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___closed__4;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___closed__5;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkDeclExt___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkDeclExt___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "baseExt"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 223, 165, 126, 7, 177, 183, 38)}};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_baseExt;
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "monoExt"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 71, 195, 20, 53, 75, 103, 187)}};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_monoExt;
static const lean_closure_object l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___boxed, .m_arity = 6, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))} };
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_impureExt;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__3_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__4;
static lean_once_cell_t l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___auto__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_mkSigDeclExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_mkSigDeclExt___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_mkSigDeclExt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__1_value;
static const lean_closure_object l_Lean_Compiler_LCNF_mkSigDeclExt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_mkSigDeclExt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__2_value)} };
static const lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__3_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "impureSigExt"};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(245, 150, 154, 56, 193, 204, 147, 237)}};
static const lean_object* l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_impureSigExt;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__0_value;
static const lean_closure_object l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_getSigCore_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getSigCore_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSigCore_x3f(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSigCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__0_value;
static const lean_array_object l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveBaseDeclCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveMonoDeclCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveImpureDeclCore___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveImpureDeclCore(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_save___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_save___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_Decl_save___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Decl_save___closed__1;
static const lean_closure_object l_Lean_Compiler_LCNF_Decl_save___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Decl_save___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_save___closed__2_value;
static const lean_closure_object l_Lean_Compiler_LCNF_Decl_save___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Decl_save___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Decl_save___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "Internal compiler error: getDecl\? on impure is unuspported for now"};
static const lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declOrderExt;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_recordFinalImpureDecl___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_recordFinalImpureDecl(lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__0 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__0_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__5 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__6 = (const lean_object*)&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__6_value;
static lean_once_cell_t l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__5(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Compiler.LCNF.PhaseExt"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__0_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Compiler.LCNF.getImpureDeclIndices"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "assertion violation: i != 0\n    "};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "assertion violation: map.size == targets.size\n  "};
static const lean_object* l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureDeclIndices(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureDeclIndices___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3496178540____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3496178540____hygCtx___hyg_2____boxed(lean_object* v_a_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3496178540____hygCtx___hyg_2_();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1977385844____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1977385844____hygCtx___hyg_2____boxed(lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1977385844____hygCtx___hyg_2_();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_975450157____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_975450157____hygCtx___hyg_2____boxed(lean_object* v_a_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_975450157____hygCtx___hyg_2_();
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_getTransparencyExt(uint8_t v_x_13_){
_start:
{
switch(v_x_13_)
{
case 0:
{
lean_object* v___x_14_; 
v___x_14_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_baseTransparentDeclsExt;
return v___x_14_;
}
case 1:
{
lean_object* v___x_15_; 
v___x_15_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_monoTransparentDeclsExt;
return v___x_15_;
}
default: 
{
lean_object* v___x_16_; 
v___x_16_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_impureTransparentDeclsExt;
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_getTransparencyExt___boxed(lean_object* v_x_17_){
_start:
{
uint8_t v_x_25__boxed_18_; lean_object* v_res_19_; 
v_x_25__boxed_18_ = lean_unbox(v_x_17_);
v_res_19_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_getTransparencyExt(v_x_25__boxed_18_);
return v_res_19_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isDeclTransparent(lean_object* v_env_23_, uint8_t v_phase_24_, lean_object* v_declName_25_){
_start:
{
lean_object* v___x_26_; uint8_t v_isModule_27_; 
v___x_26_ = l_Lean_Environment_header(v_env_23_);
v_isModule_27_ = lean_ctor_get_uint8(v___x_26_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_26_);
if (v_isModule_27_ == 0)
{
uint8_t v___x_28_; 
lean_dec_ref(v_env_23_);
v___x_28_ = 1;
return v___x_28_;
}
else
{
lean_object* v___x_29_; lean_object* v_asyncMode_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v_snd_34_; uint8_t v___x_35_; 
v___x_29_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_getTransparencyExt(v_phase_24_);
v_asyncMode_30_ = lean_ctor_get(v___x_29_, 2);
lean_inc(v_asyncMode_30_);
v___x_31_ = ((lean_object*)(l_Lean_Compiler_LCNF_isDeclTransparent___closed__0));
v___x_32_ = lean_box(0);
v___x_33_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_31_, v___x_29_, v_env_23_, v_asyncMode_30_, v___x_32_);
lean_dec(v_asyncMode_30_);
lean_dec_ref(v___x_29_);
v_snd_34_ = lean_ctor_get(v___x_33_, 1);
lean_inc(v_snd_34_);
lean_dec(v___x_33_);
v___x_35_ = l_Lean_NameSet_contains(v_snd_34_, v_declName_25_);
lean_dec(v_snd_34_);
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isDeclTransparent___boxed(lean_object* v_env_36_, lean_object* v_phase_37_, lean_object* v_declName_38_){
_start:
{
uint8_t v_phase_boxed_39_; uint8_t v_res_40_; lean_object* v_r_41_; 
v_phase_boxed_39_ = lean_unbox(v_phase_37_);
v_res_40_ = l_Lean_Compiler_LCNF_isDeclTransparent(v_env_36_, v_phase_boxed_39_, v_declName_38_);
lean_dec(v_declName_38_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclTransparent___lam__0(lean_object* v_declName_42_, lean_object* v_s_43_){
_start:
{
lean_object* v_fst_44_; lean_object* v_snd_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_54_; 
v_fst_44_ = lean_ctor_get(v_s_43_, 0);
v_snd_45_ = lean_ctor_get(v_s_43_, 1);
v_isSharedCheck_54_ = !lean_is_exclusive(v_s_43_);
if (v_isSharedCheck_54_ == 0)
{
v___x_47_ = v_s_43_;
v_isShared_48_ = v_isSharedCheck_54_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_snd_45_);
lean_inc(v_fst_44_);
lean_dec(v_s_43_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_54_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_52_; 
lean_inc(v_declName_42_);
v___x_49_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_49_, 0, v_declName_42_);
lean_ctor_set(v___x_49_, 1, v_fst_44_);
v___x_50_ = l_Lean_NameSet_insert(v_snd_45_, v_declName_42_);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 1, v___x_50_);
lean_ctor_set(v___x_47_, 0, v___x_49_);
v___x_52_ = v___x_47_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_49_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v___x_50_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclTransparent(lean_object* v_env_55_, uint8_t v_phase_56_, lean_object* v_declName_57_){
_start:
{
uint8_t v___x_58_; 
lean_inc_ref(v_env_55_);
v___x_58_ = l_Lean_Compiler_LCNF_isDeclTransparent(v_env_55_, v_phase_56_, v_declName_57_);
if (v___x_58_ == 0)
{
lean_object* v___x_59_; lean_object* v_asyncMode_60_; lean_object* v___f_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_59_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_getTransparencyExt(v_phase_56_);
v_asyncMode_60_ = lean_ctor_get(v___x_59_, 2);
lean_inc(v_asyncMode_60_);
v___f_61_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_setDeclTransparent___lam__0), 2, 1);
lean_closure_set(v___f_61_, 0, v_declName_57_);
v___x_62_ = lean_box(0);
v___x_63_ = l_Lean_EnvExtension_modifyState___redArg(v___x_59_, v_env_55_, v___f_61_, v_asyncMode_60_, v___x_62_);
lean_dec(v_asyncMode_60_);
return v___x_63_;
}
else
{
lean_dec(v_declName_57_);
return v_env_55_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclTransparent___boxed(lean_object* v_env_64_, lean_object* v_phase_65_, lean_object* v_declName_66_){
_start:
{
uint8_t v_phase_boxed_67_; lean_object* v_res_68_; 
v_phase_boxed_67_ = lean_unbox(v_phase_65_);
v_res_68_ = l_Lean_Compiler_LCNF_setDeclTransparent(v_env_64_, v_phase_boxed_67_, v_declName_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___lam__0(lean_object* v_ps_69_, lean_object* v_x_70_, lean_object* v_v_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = lean_array_push(v_ps_69_, v_v_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___lam__0___boxed(lean_object* v_ps_73_, lean_object* v_x_74_, lean_object* v_v_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___lam__0(v_ps_73_, v_x_74_, v_v_75_);
lean_dec(v_x_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_f_77_, lean_object* v_keys_78_, lean_object* v_vals_79_, lean_object* v_i_80_, lean_object* v_acc_81_){
_start:
{
lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_82_ = lean_array_get_size(v_keys_78_);
v___x_83_ = lean_nat_dec_lt(v_i_80_, v___x_82_);
if (v___x_83_ == 0)
{
lean_dec(v_i_80_);
lean_dec(v_f_77_);
return v_acc_81_;
}
else
{
lean_object* v_k_84_; lean_object* v_v_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v_k_84_ = lean_array_fget_borrowed(v_keys_78_, v_i_80_);
v_v_85_ = lean_array_fget_borrowed(v_vals_79_, v_i_80_);
lean_inc(v_f_77_);
lean_inc(v_v_85_);
lean_inc(v_k_84_);
v___x_86_ = lean_apply_3(v_f_77_, v_acc_81_, v_k_84_, v_v_85_);
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_nat_add(v_i_80_, v___x_87_);
lean_dec(v_i_80_);
v_i_80_ = v___x_88_;
v_acc_81_ = v___x_86_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_f_90_, lean_object* v_keys_91_, lean_object* v_vals_92_, lean_object* v_i_93_, lean_object* v_acc_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg(v_f_90_, v_keys_91_, v_vals_92_, v_i_93_, v_acc_94_);
lean_dec_ref(v_vals_92_);
lean_dec_ref(v_keys_91_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(lean_object* v_f_96_, lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
if (lean_obj_tag(v_x_97_) == 0)
{
lean_object* v_es_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v_es_99_ = lean_ctor_get(v_x_97_, 0);
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_array_get_size(v_es_99_);
v___x_102_ = lean_nat_dec_lt(v___x_100_, v___x_101_);
if (v___x_102_ == 0)
{
lean_dec(v_f_96_);
return v_x_98_;
}
else
{
uint8_t v___x_103_; 
v___x_103_ = lean_nat_dec_le(v___x_101_, v___x_101_);
if (v___x_103_ == 0)
{
if (v___x_102_ == 0)
{
lean_dec(v_f_96_);
return v_x_98_;
}
else
{
size_t v___x_104_; size_t v___x_105_; lean_object* v___x_106_; 
v___x_104_ = ((size_t)0ULL);
v___x_105_ = lean_usize_of_nat(v___x_101_);
v___x_106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(v_f_96_, v_es_99_, v___x_104_, v___x_105_, v_x_98_);
return v___x_106_;
}
}
else
{
size_t v___x_107_; size_t v___x_108_; lean_object* v___x_109_; 
v___x_107_ = ((size_t)0ULL);
v___x_108_ = lean_usize_of_nat(v___x_101_);
v___x_109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(v_f_96_, v_es_99_, v___x_107_, v___x_108_, v_x_98_);
return v___x_109_;
}
}
}
else
{
lean_object* v_ks_110_; lean_object* v_vs_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_ks_110_ = lean_ctor_get(v_x_97_, 0);
v_vs_111_ = lean_ctor_get(v_x_97_, 1);
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg(v_f_96_, v_ks_110_, v_vs_111_, v___x_112_, v_x_98_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_114_, lean_object* v_as_115_, size_t v_i_116_, size_t v_stop_117_, lean_object* v_b_118_){
_start:
{
lean_object* v___y_120_; uint8_t v___x_124_; 
v___x_124_ = lean_usize_dec_eq(v_i_116_, v_stop_117_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
v___x_125_ = lean_array_uget_borrowed(v_as_115_, v_i_116_);
switch(lean_obj_tag(v___x_125_))
{
case 0:
{
lean_object* v_key_126_; lean_object* v_val_127_; lean_object* v___x_128_; 
v_key_126_ = lean_ctor_get(v___x_125_, 0);
v_val_127_ = lean_ctor_get(v___x_125_, 1);
lean_inc(v_f_114_);
lean_inc(v_val_127_);
lean_inc(v_key_126_);
v___x_128_ = lean_apply_3(v_f_114_, v_b_118_, v_key_126_, v_val_127_);
v___y_120_ = v___x_128_;
goto v___jp_119_;
}
case 1:
{
lean_object* v_node_129_; lean_object* v___x_130_; 
v_node_129_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_f_114_);
v___x_130_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_114_, v_node_129_, v_b_118_);
v___y_120_ = v___x_130_;
goto v___jp_119_;
}
default: 
{
v___y_120_ = v_b_118_;
goto v___jp_119_;
}
}
}
else
{
lean_dec(v_f_114_);
return v_b_118_;
}
v___jp_119_:
{
size_t v___x_121_; size_t v___x_122_; 
v___x_121_ = ((size_t)1ULL);
v___x_122_ = lean_usize_add(v_i_116_, v___x_121_);
v_i_116_ = v___x_122_;
v_b_118_ = v___y_120_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_131_, lean_object* v_as_132_, lean_object* v_i_133_, lean_object* v_stop_134_, lean_object* v_b_135_){
_start:
{
size_t v_i_boxed_136_; size_t v_stop_boxed_137_; lean_object* v_res_138_; 
v_i_boxed_136_ = lean_unbox_usize(v_i_133_);
lean_dec(v_i_133_);
v_stop_boxed_137_ = lean_unbox_usize(v_stop_134_);
lean_dec(v_stop_134_);
v_res_138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(v_f_131_, v_as_132_, v_i_boxed_136_, v_stop_boxed_137_, v_b_135_);
lean_dec_ref(v_as_132_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_139_, lean_object* v_x_140_, lean_object* v_x_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_139_, v_x_140_, v_x_141_);
lean_dec_ref(v_x_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg___lam__0(lean_object* v_f_143_, lean_object* v_x1_144_, lean_object* v_x2_145_, lean_object* v_x3_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = lean_apply_3(v_f_143_, v_x1_144_, v_x2_145_, v_x3_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(lean_object* v_map_148_, lean_object* v_f_149_, lean_object* v_init_150_){
_start:
{
lean_object* v___f_151_; lean_object* v___x_152_; 
v___f_151_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_151_, 0, v_f_149_);
v___x_152_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v___f_151_, v_map_148_, v_init_150_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg___boxed(lean_object* v_map_153_, lean_object* v_f_154_, lean_object* v_init_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_map_153_, v_f_154_, v_init_155_);
lean_dec_ref(v_map_153_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(lean_object* v_lt_157_, lean_object* v_as_158_, lean_object* v_lo_159_, lean_object* v_hi_160_){
_start:
{
uint8_t v___x_161_; 
v___x_161_ = lean_nat_dec_lt(v_lo_159_, v_hi_160_);
if (v___x_161_ == 0)
{
lean_dec(v_lo_159_);
lean_dec_ref(v_lt_157_);
return v_as_158_;
}
else
{
lean_object* v___x_162_; lean_object* v_fst_163_; lean_object* v_snd_164_; uint8_t v___x_165_; 
lean_inc(v_lo_159_);
lean_inc_ref(v_lt_157_);
v___x_162_ = l_Array_qpartition___redArg(v_as_158_, v_lt_157_, v_lo_159_, v_hi_160_);
v_fst_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_fst_163_);
v_snd_164_ = lean_ctor_get(v___x_162_, 1);
lean_inc(v_snd_164_);
lean_dec_ref(v___x_162_);
v___x_165_ = lean_nat_dec_le(v_hi_160_, v_fst_163_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
lean_inc_ref(v_lt_157_);
v___x_166_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_157_, v_snd_164_, v_lo_159_, v_fst_163_);
v___x_167_ = lean_unsigned_to_nat(1u);
v___x_168_ = lean_nat_add(v_fst_163_, v___x_167_);
lean_dec(v_fst_163_);
v_as_158_ = v___x_166_;
v_lo_159_ = v___x_168_;
goto _start;
}
else
{
lean_dec(v_fst_163_);
lean_dec(v_lo_159_);
lean_dec_ref(v_lt_157_);
return v_snd_164_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg___boxed(lean_object* v_lt_170_, lean_object* v_as_171_, lean_object* v_lo_172_, lean_object* v_hi_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_170_, v_as_171_, v_lo_172_, v_hi_173_);
lean_dec(v_hi_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(lean_object* v_s_178_, lean_object* v_lt_179_){
_start:
{
lean_object* v___f_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v_decls_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___f_180_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__0));
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___closed__1));
v_decls_183_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_s_178_, v___f_180_, v___x_182_);
v___x_184_ = lean_array_get_size(v_decls_183_);
v___x_185_ = lean_nat_dec_eq(v___x_184_, v___x_181_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___y_189_; uint8_t v___x_193_; 
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_nat_sub(v___x_184_, v___x_186_);
v___x_193_ = lean_nat_dec_le(v___x_181_, v___x_187_);
if (v___x_193_ == 0)
{
lean_inc(v___x_187_);
v___y_189_ = v___x_187_;
goto v___jp_188_;
}
else
{
v___y_189_ = v___x_181_;
goto v___jp_188_;
}
v___jp_188_:
{
uint8_t v___x_190_; 
v___x_190_ = lean_nat_dec_le(v___y_189_, v___x_187_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; 
lean_dec(v___x_187_);
lean_inc(v___y_189_);
v___x_191_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_179_, v_decls_183_, v___y_189_, v___y_189_);
lean_dec(v___y_189_);
return v___x_191_;
}
else
{
lean_object* v___x_192_; 
v___x_192_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_179_, v_decls_183_, v___y_189_, v___x_187_);
lean_dec(v___x_187_);
return v___x_192_;
}
}
}
else
{
lean_dec_ref(v_lt_179_);
return v_decls_183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg___boxed(lean_object* v_s_194_, lean_object* v_lt_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(v_s_194_, v_lt_195_);
lean_dec_ref(v_s_194_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries(uint8_t v_pu_197_, lean_object* v_00_u03b2_198_, lean_object* v_s_199_, lean_object* v_lt_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(v_s_199_, v_lt_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___boxed(lean_object* v_pu_202_, lean_object* v_00_u03b2_203_, lean_object* v_s_204_, lean_object* v_lt_205_){
_start:
{
uint8_t v_pu_boxed_206_; lean_object* v_res_207_; 
v_pu_boxed_206_ = lean_unbox(v_pu_202_);
v_res_207_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries(v_pu_boxed_206_, v_00_u03b2_203_, v_s_204_, v_lt_205_);
lean_dec_ref(v_s_204_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0(lean_object* v_00_u03c3_208_, lean_object* v_00_u03b2_209_, lean_object* v_map_210_, lean_object* v_f_211_, lean_object* v_init_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_map_210_, v_f_211_, v_init_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___boxed(lean_object* v_00_u03c3_214_, lean_object* v_00_u03b2_215_, lean_object* v_map_216_, lean_object* v_f_217_, lean_object* v_init_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0(v_00_u03c3_214_, v_00_u03b2_215_, v_map_216_, v_f_217_, v_init_218_);
lean_dec_ref(v_map_216_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1(lean_object* v_00_u03b2_220_, lean_object* v_lt_221_, lean_object* v_n_222_, lean_object* v_as_223_, lean_object* v_lo_224_, lean_object* v_hi_225_, lean_object* v_w_226_, lean_object* v_hlo_227_, lean_object* v_hhi_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___redArg(v_lt_221_, v_as_223_, v_lo_224_, v_hi_225_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1___boxed(lean_object* v_00_u03b2_230_, lean_object* v_lt_231_, lean_object* v_n_232_, lean_object* v_as_233_, lean_object* v_lo_234_, lean_object* v_hi_235_, lean_object* v_w_236_, lean_object* v_hlo_237_, lean_object* v_hhi_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__1(v_00_u03b2_230_, v_lt_231_, v_n_232_, v_as_233_, v_lo_234_, v_hi_235_, v_w_236_, v_hlo_237_, v_hhi_238_);
lean_dec(v_hi_235_);
lean_dec(v_n_232_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___redArg(lean_object* v_map_240_, lean_object* v_f_241_, lean_object* v_init_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_241_, v_map_240_, v_init_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___redArg___boxed(lean_object* v_map_244_, lean_object* v_f_245_, lean_object* v_init_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___redArg(v_map_244_, v_f_245_, v_init_246_);
lean_dec_ref(v_map_244_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0(lean_object* v_00_u03c3_248_, lean_object* v_00_u03b2_249_, lean_object* v_map_250_, lean_object* v_f_251_, lean_object* v_init_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_251_, v_map_250_, v_init_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0___boxed(lean_object* v_00_u03c3_254_, lean_object* v_00_u03b2_255_, lean_object* v_map_256_, lean_object* v_f_257_, lean_object* v_init_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0(v_00_u03c3_254_, v_00_u03b2_255_, v_map_256_, v_f_257_, v_init_258_);
lean_dec_ref(v_map_256_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_260_, lean_object* v_00_u03b1_261_, lean_object* v_00_u03b2_262_, lean_object* v_f_263_, lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___redArg(v_f_263_, v_x_264_, v_x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_267_, lean_object* v_00_u03b1_268_, lean_object* v_00_u03b2_269_, lean_object* v_f_270_, lean_object* v_x_271_, lean_object* v_x_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1(v_00_u03c3_267_, v_00_u03b1_268_, v_00_u03b2_269_, v_f_270_, v_x_271_, v_x_272_);
lean_dec_ref(v_x_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_274_, lean_object* v_00_u03b2_275_, lean_object* v_00_u03c3_276_, lean_object* v_f_277_, lean_object* v_as_278_, size_t v_i_279_, size_t v_stop_280_, lean_object* v_b_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___redArg(v_f_277_, v_as_278_, v_i_279_, v_stop_280_, v_b_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_283_, lean_object* v_00_u03b2_284_, lean_object* v_00_u03c3_285_, lean_object* v_f_286_, lean_object* v_as_287_, lean_object* v_i_288_, lean_object* v_stop_289_, lean_object* v_b_290_){
_start:
{
size_t v_i_boxed_291_; size_t v_stop_boxed_292_; lean_object* v_res_293_; 
v_i_boxed_291_ = lean_unbox_usize(v_i_288_);
lean_dec(v_i_288_);
v_stop_boxed_292_ = lean_unbox_usize(v_stop_289_);
lean_dec(v_stop_289_);
v_res_293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_283_, v_00_u03b2_284_, v_00_u03c3_285_, v_f_286_, v_as_287_, v_i_boxed_291_, v_stop_boxed_292_, v_b_290_);
lean_dec_ref(v_as_287_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03c3_294_, lean_object* v_00_u03b1_295_, lean_object* v_00_u03b2_296_, lean_object* v_f_297_, lean_object* v_keys_298_, lean_object* v_vals_299_, lean_object* v_heq_300_, lean_object* v_i_301_, lean_object* v_acc_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___redArg(v_f_297_, v_keys_298_, v_vals_299_, v_i_301_, v_acc_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03c3_304_, lean_object* v_00_u03b1_305_, lean_object* v_00_u03b2_306_, lean_object* v_f_307_, lean_object* v_keys_308_, lean_object* v_vals_309_, lean_object* v_heq_310_, lean_object* v_i_311_, lean_object* v_acc_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0_spec__0_spec__1_spec__4(v_00_u03c3_304_, v_00_u03b1_305_, v_00_u03b2_306_, v_f_307_, v_keys_308_, v_vals_309_, v_heq_310_, v_i_311_, v_acc_312_);
lean_dec_ref(v_vals_309_);
lean_dec_ref(v_keys_308_);
return v_res_313_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_314_, lean_object* v_i_315_, lean_object* v_k_316_){
_start:
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = lean_array_get_size(v_keys_314_);
v___x_318_ = lean_nat_dec_lt(v_i_315_, v___x_317_);
if (v___x_318_ == 0)
{
lean_dec(v_i_315_);
return v___x_318_;
}
else
{
lean_object* v_k_x27_319_; uint8_t v___x_320_; 
v_k_x27_319_ = lean_array_fget_borrowed(v_keys_314_, v_i_315_);
v___x_320_ = lean_name_eq(v_k_316_, v_k_x27_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_unsigned_to_nat(1u);
v___x_322_ = lean_nat_add(v_i_315_, v___x_321_);
lean_dec(v_i_315_);
v_i_315_ = v___x_322_;
goto _start;
}
else
{
lean_dec(v_i_315_);
return v___x_320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_324_, lean_object* v_i_325_, lean_object* v_k_326_){
_start:
{
uint8_t v_res_327_; lean_object* v_r_328_; 
v_res_327_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(v_keys_324_, v_i_325_, v_k_326_);
lean_dec(v_k_326_);
lean_dec_ref(v_keys_324_);
v_r_328_ = lean_box(v_res_327_);
return v_r_328_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_329_; size_t v___x_330_; size_t v___x_331_; 
v___x_329_ = ((size_t)5ULL);
v___x_330_ = ((size_t)1ULL);
v___x_331_ = lean_usize_shift_left(v___x_330_, v___x_329_);
return v___x_331_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_332_; size_t v___x_333_; size_t v___x_334_; 
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__0);
v___x_334_ = lean_usize_sub(v___x_333_, v___x_332_);
return v___x_334_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(lean_object* v_x_335_, size_t v_x_336_, lean_object* v_x_337_){
_start:
{
if (lean_obj_tag(v_x_335_) == 0)
{
lean_object* v_es_338_; lean_object* v___x_339_; size_t v___x_340_; size_t v___x_341_; size_t v___x_342_; lean_object* v_j_343_; lean_object* v___x_344_; 
v_es_338_ = lean_ctor_get(v_x_335_, 0);
lean_inc_ref(v_es_338_);
lean_dec_ref(v_x_335_);
v___x_339_ = lean_box(2);
v___x_340_ = ((size_t)5ULL);
v___x_341_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1);
v___x_342_ = lean_usize_land(v_x_336_, v___x_341_);
v_j_343_ = lean_usize_to_nat(v___x_342_);
v___x_344_ = lean_array_get(v___x_339_, v_es_338_, v_j_343_);
lean_dec(v_j_343_);
lean_dec_ref(v_es_338_);
switch(lean_obj_tag(v___x_344_))
{
case 0:
{
lean_object* v_key_345_; uint8_t v___x_346_; 
v_key_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_key_345_);
lean_dec_ref(v___x_344_);
v___x_346_ = lean_name_eq(v_x_337_, v_key_345_);
lean_dec(v_key_345_);
return v___x_346_;
}
case 1:
{
lean_object* v_node_347_; size_t v___x_348_; 
v_node_347_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_node_347_);
lean_dec_ref(v___x_344_);
v___x_348_ = lean_usize_shift_right(v_x_336_, v___x_340_);
v_x_335_ = v_node_347_;
v_x_336_ = v___x_348_;
goto _start;
}
default: 
{
uint8_t v___x_350_; 
v___x_350_ = 0;
return v___x_350_;
}
}
}
else
{
lean_object* v_ks_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v_ks_351_ = lean_ctor_get(v_x_335_, 0);
lean_inc_ref(v_ks_351_);
lean_dec_ref(v_x_335_);
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(v_ks_351_, v___x_352_, v_x_337_);
lean_dec_ref(v_ks_351_);
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___boxed(lean_object* v_x_354_, lean_object* v_x_355_, lean_object* v_x_356_){
_start:
{
size_t v_x_433__boxed_357_; uint8_t v_res_358_; lean_object* v_r_359_; 
v_x_433__boxed_357_ = lean_unbox_usize(v_x_355_);
lean_dec(v_x_355_);
v_res_358_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(v_x_354_, v_x_433__boxed_357_, v_x_356_);
lean_dec(v_x_356_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_360_; uint64_t v___x_361_; 
v___x_360_ = lean_unsigned_to_nat(1723u);
v___x_361_ = lean_uint64_of_nat(v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
uint64_t v___y_365_; 
if (lean_obj_tag(v_x_363_) == 0)
{
uint64_t v___x_368_; 
v___x_368_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
v___y_365_ = v___x_368_;
goto v___jp_364_;
}
else
{
uint64_t v_hash_369_; 
v_hash_369_ = lean_ctor_get_uint64(v_x_363_, sizeof(void*)*2);
v___y_365_ = v_hash_369_;
goto v___jp_364_;
}
v___jp_364_:
{
size_t v___x_366_; uint8_t v___x_367_; 
v___x_366_ = lean_uint64_to_usize(v___y_365_);
v___x_367_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(v_x_362_, v___x_366_, v_x_363_);
return v___x_367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___boxed(lean_object* v_x_370_, lean_object* v_x_371_){
_start:
{
uint8_t v_res_372_; lean_object* v_r_373_; 
v_res_372_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(v_x_370_, v_x_371_);
lean_dec(v_x_371_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_374_, lean_object* v_x_375_, lean_object* v_x_376_, lean_object* v_x_377_){
_start:
{
lean_object* v_ks_378_; lean_object* v_vs_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_403_; 
v_ks_378_ = lean_ctor_get(v_x_374_, 0);
v_vs_379_ = lean_ctor_get(v_x_374_, 1);
v_isSharedCheck_403_ = !lean_is_exclusive(v_x_374_);
if (v_isSharedCheck_403_ == 0)
{
v___x_381_ = v_x_374_;
v_isShared_382_ = v_isSharedCheck_403_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_vs_379_);
lean_inc(v_ks_378_);
lean_dec(v_x_374_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_403_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = lean_array_get_size(v_ks_378_);
v___x_384_ = lean_nat_dec_lt(v_x_375_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
lean_dec(v_x_375_);
v___x_385_ = lean_array_push(v_ks_378_, v_x_376_);
v___x_386_ = lean_array_push(v_vs_379_, v_x_377_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 1, v___x_386_);
lean_ctor_set(v___x_381_, 0, v___x_385_);
v___x_388_ = v___x_381_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
else
{
lean_object* v_k_x27_390_; uint8_t v___x_391_; 
v_k_x27_390_ = lean_array_fget_borrowed(v_ks_378_, v_x_375_);
v___x_391_ = lean_name_eq(v_x_376_, v_k_x27_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_393_; 
if (v_isShared_382_ == 0)
{
v___x_393_ = v___x_381_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_ks_378_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_vs_379_);
v___x_393_ = v_reuseFailAlloc_397_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_unsigned_to_nat(1u);
v___x_395_ = lean_nat_add(v_x_375_, v___x_394_);
lean_dec(v_x_375_);
v_x_374_ = v___x_393_;
v_x_375_ = v___x_395_;
goto _start;
}
}
else
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_398_ = lean_array_fset(v_ks_378_, v_x_375_, v_x_376_);
v___x_399_ = lean_array_fset(v_vs_379_, v_x_375_, v_x_377_);
lean_dec(v_x_375_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 1, v___x_399_);
lean_ctor_set(v___x_381_, 0, v___x_398_);
v___x_401_ = v___x_381_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v___x_399_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4___redArg(lean_object* v_n_404_, lean_object* v_k_405_, lean_object* v_v_406_){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5___redArg(v_n_404_, v___x_407_, v_k_405_, v_v_406_);
return v___x_408_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(lean_object* v_x_410_, size_t v_x_411_, size_t v_x_412_, lean_object* v_x_413_, lean_object* v_x_414_){
_start:
{
if (lean_obj_tag(v_x_410_) == 0)
{
lean_object* v_es_415_; size_t v___x_416_; size_t v___x_417_; size_t v___x_418_; size_t v___x_419_; lean_object* v_j_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v_es_415_ = lean_ctor_get(v_x_410_, 0);
v___x_416_ = ((size_t)5ULL);
v___x_417_ = ((size_t)1ULL);
v___x_418_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1);
v___x_419_ = lean_usize_land(v_x_411_, v___x_418_);
v_j_420_ = lean_usize_to_nat(v___x_419_);
v___x_421_ = lean_array_get_size(v_es_415_);
v___x_422_ = lean_nat_dec_lt(v_j_420_, v___x_421_);
if (v___x_422_ == 0)
{
lean_dec(v_j_420_);
lean_dec(v_x_414_);
lean_dec(v_x_413_);
return v_x_410_;
}
else
{
lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_459_; 
lean_inc_ref(v_es_415_);
v_isSharedCheck_459_ = !lean_is_exclusive(v_x_410_);
if (v_isSharedCheck_459_ == 0)
{
lean_object* v_unused_460_; 
v_unused_460_ = lean_ctor_get(v_x_410_, 0);
lean_dec(v_unused_460_);
v___x_424_ = v_x_410_;
v_isShared_425_ = v_isSharedCheck_459_;
goto v_resetjp_423_;
}
else
{
lean_dec(v_x_410_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_459_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v_v_426_; lean_object* v___x_427_; lean_object* v_xs_x27_428_; lean_object* v___y_430_; 
v_v_426_ = lean_array_fget(v_es_415_, v_j_420_);
v___x_427_ = lean_box(0);
v_xs_x27_428_ = lean_array_fset(v_es_415_, v_j_420_, v___x_427_);
switch(lean_obj_tag(v_v_426_))
{
case 0:
{
lean_object* v_key_435_; lean_object* v_val_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_446_; 
v_key_435_ = lean_ctor_get(v_v_426_, 0);
v_val_436_ = lean_ctor_get(v_v_426_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v_v_426_);
if (v_isSharedCheck_446_ == 0)
{
v___x_438_ = v_v_426_;
v_isShared_439_ = v_isSharedCheck_446_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_val_436_);
lean_inc(v_key_435_);
lean_dec(v_v_426_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_446_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
uint8_t v___x_440_; 
v___x_440_ = lean_name_eq(v_x_413_, v_key_435_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; 
lean_del_object(v___x_438_);
v___x_441_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_435_, v_val_436_, v_x_413_, v_x_414_);
v___x_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
v___y_430_ = v___x_442_;
goto v___jp_429_;
}
else
{
lean_object* v___x_444_; 
lean_dec(v_val_436_);
lean_dec(v_key_435_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 1, v_x_414_);
lean_ctor_set(v___x_438_, 0, v_x_413_);
v___x_444_ = v___x_438_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_x_413_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_x_414_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
v___y_430_ = v___x_444_;
goto v___jp_429_;
}
}
}
}
case 1:
{
lean_object* v_node_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_457_; 
v_node_447_ = lean_ctor_get(v_v_426_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v_v_426_);
if (v_isSharedCheck_457_ == 0)
{
v___x_449_ = v_v_426_;
v_isShared_450_ = v_isSharedCheck_457_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_node_447_);
lean_dec(v_v_426_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_457_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
size_t v___x_451_; size_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_451_ = lean_usize_shift_right(v_x_411_, v___x_416_);
v___x_452_ = lean_usize_add(v_x_412_, v___x_417_);
v___x_453_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_node_447_, v___x_451_, v___x_452_, v_x_413_, v_x_414_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_453_);
v___x_455_ = v___x_449_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
v___y_430_ = v___x_455_;
goto v___jp_429_;
}
}
}
default: 
{
lean_object* v___x_458_; 
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v_x_413_);
lean_ctor_set(v___x_458_, 1, v_x_414_);
v___y_430_ = v___x_458_;
goto v___jp_429_;
}
}
v___jp_429_:
{
lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_431_ = lean_array_fset(v_xs_x27_428_, v_j_420_, v___y_430_);
lean_dec(v_j_420_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_431_);
v___x_433_ = v___x_424_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
else
{
lean_object* v_ks_461_; lean_object* v_vs_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_482_; 
v_ks_461_ = lean_ctor_get(v_x_410_, 0);
v_vs_462_ = lean_ctor_get(v_x_410_, 1);
v_isSharedCheck_482_ = !lean_is_exclusive(v_x_410_);
if (v_isSharedCheck_482_ == 0)
{
v___x_464_ = v_x_410_;
v_isShared_465_ = v_isSharedCheck_482_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_vs_462_);
lean_inc(v_ks_461_);
lean_dec(v_x_410_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_482_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_ks_461_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_vs_462_);
v___x_467_ = v_reuseFailAlloc_481_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v_newNode_468_; uint8_t v___y_470_; size_t v___x_476_; uint8_t v___x_477_; 
v_newNode_468_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4___redArg(v___x_467_, v_x_413_, v_x_414_);
v___x_476_ = ((size_t)7ULL);
v___x_477_ = lean_usize_dec_le(v___x_476_, v_x_412_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_478_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_468_);
v___x_479_ = lean_unsigned_to_nat(4u);
v___x_480_ = lean_nat_dec_lt(v___x_478_, v___x_479_);
lean_dec(v___x_478_);
v___y_470_ = v___x_480_;
goto v___jp_469_;
}
else
{
v___y_470_ = v___x_477_;
goto v___jp_469_;
}
v___jp_469_:
{
if (v___y_470_ == 0)
{
lean_object* v_ks_471_; lean_object* v_vs_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_ks_471_ = lean_ctor_get(v_newNode_468_, 0);
lean_inc_ref(v_ks_471_);
v_vs_472_ = lean_ctor_get(v_newNode_468_, 1);
lean_inc_ref(v_vs_472_);
lean_dec_ref(v_newNode_468_);
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___closed__0);
v___x_475_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(v_x_412_, v_ks_471_, v_vs_472_, v___x_473_, v___x_474_);
lean_dec_ref(v_vs_472_);
lean_dec_ref(v_ks_471_);
return v___x_475_;
}
else
{
return v_newNode_468_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(size_t v_depth_483_, lean_object* v_keys_484_, lean_object* v_vals_485_, lean_object* v_i_486_, lean_object* v_entries_487_){
_start:
{
lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = lean_array_get_size(v_keys_484_);
v___x_489_ = lean_nat_dec_lt(v_i_486_, v___x_488_);
if (v___x_489_ == 0)
{
lean_dec(v_i_486_);
return v_entries_487_;
}
else
{
lean_object* v_k_490_; lean_object* v_v_491_; uint64_t v___y_493_; 
v_k_490_ = lean_array_fget_borrowed(v_keys_484_, v_i_486_);
v_v_491_ = lean_array_fget_borrowed(v_vals_485_, v_i_486_);
if (lean_obj_tag(v_k_490_) == 0)
{
uint64_t v___x_504_; 
v___x_504_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
v___y_493_ = v___x_504_;
goto v___jp_492_;
}
else
{
uint64_t v_hash_505_; 
v_hash_505_ = lean_ctor_get_uint64(v_k_490_, sizeof(void*)*2);
v___y_493_ = v_hash_505_;
goto v___jp_492_;
}
v___jp_492_:
{
size_t v_h_494_; size_t v___x_495_; lean_object* v___x_496_; size_t v___x_497_; size_t v___x_498_; size_t v___x_499_; size_t v_h_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v_h_494_ = lean_uint64_to_usize(v___y_493_);
v___x_495_ = ((size_t)5ULL);
v___x_496_ = lean_unsigned_to_nat(1u);
v___x_497_ = ((size_t)1ULL);
v___x_498_ = lean_usize_sub(v_depth_483_, v___x_497_);
v___x_499_ = lean_usize_mul(v___x_495_, v___x_498_);
v_h_500_ = lean_usize_shift_right(v_h_494_, v___x_499_);
v___x_501_ = lean_nat_add(v_i_486_, v___x_496_);
lean_dec(v_i_486_);
lean_inc(v_v_491_);
lean_inc(v_k_490_);
v___x_502_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_entries_487_, v_h_500_, v_depth_483_, v_k_490_, v_v_491_);
v_i_486_ = v___x_501_;
v_entries_487_ = v___x_502_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_506_, lean_object* v_keys_507_, lean_object* v_vals_508_, lean_object* v_i_509_, lean_object* v_entries_510_){
_start:
{
size_t v_depth_boxed_511_; lean_object* v_res_512_; 
v_depth_boxed_511_ = lean_unbox_usize(v_depth_506_);
lean_dec(v_depth_506_);
v_res_512_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(v_depth_boxed_511_, v_keys_507_, v_vals_508_, v_i_509_, v_entries_510_);
lean_dec_ref(v_vals_508_);
lean_dec_ref(v_keys_507_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg___boxed(lean_object* v_x_513_, lean_object* v_x_514_, lean_object* v_x_515_, lean_object* v_x_516_, lean_object* v_x_517_){
_start:
{
size_t v_x_589__boxed_518_; size_t v_x_590__boxed_519_; lean_object* v_res_520_; 
v_x_589__boxed_518_ = lean_unbox_usize(v_x_514_);
lean_dec(v_x_514_);
v_x_590__boxed_519_ = lean_unbox_usize(v_x_515_);
lean_dec(v_x_515_);
v_res_520_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_x_513_, v_x_589__boxed_518_, v_x_590__boxed_519_, v_x_516_, v_x_517_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(lean_object* v_x_521_, lean_object* v_x_522_, lean_object* v_x_523_){
_start:
{
uint64_t v___y_525_; 
if (lean_obj_tag(v_x_522_) == 0)
{
uint64_t v___x_529_; 
v___x_529_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
v___y_525_ = v___x_529_;
goto v___jp_524_;
}
else
{
uint64_t v_hash_530_; 
v_hash_530_ = lean_ctor_get_uint64(v_x_522_, sizeof(void*)*2);
v___y_525_ = v_hash_530_;
goto v___jp_524_;
}
v___jp_524_:
{
size_t v___x_526_; size_t v___x_527_; lean_object* v___x_528_; 
v___x_526_ = lean_uint64_to_usize(v___y_525_);
v___x_527_ = ((size_t)1ULL);
v___x_528_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_x_521_, v___x_526_, v___x_527_, v_x_522_, v_x_523_);
return v___x_528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___lam__0(lean_object* v_oldState_531_, lean_object* v_otherState_532_, lean_object* v_k_533_, lean_object* v_v_534_){
_start:
{
uint8_t v___x_535_; 
v___x_535_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(v_oldState_531_, v_k_533_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; 
v___x_536_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_otherState_532_, v_k_533_, v_v_534_);
return v___x_536_;
}
else
{
lean_dec(v_v_534_);
lean_dec(v_k_533_);
return v_otherState_532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg(lean_object* v_oldState_537_, lean_object* v_newState_538_, lean_object* v_otherState_539_){
_start:
{
lean_object* v___f_540_; lean_object* v___x_541_; 
v___f_540_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_540_, 0, v_oldState_537_);
v___x_541_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_newState_538_, v___f_540_, v_otherState_539_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg___boxed(lean_object* v_oldState_542_, lean_object* v_newState_543_, lean_object* v_otherState_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg(v_oldState_542_, v_newState_543_, v_otherState_544_);
lean_dec_ref(v_newState_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn(lean_object* v_00_u03b2_546_, uint8_t v_phase_547_, lean_object* v_oldState_548_, lean_object* v_newState_549_, lean_object* v_x_550_, lean_object* v_otherState_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___redArg(v_oldState_548_, v_newState_549_, v_otherState_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___boxed(lean_object* v_00_u03b2_553_, lean_object* v_phase_554_, lean_object* v_oldState_555_, lean_object* v_newState_556_, lean_object* v_x_557_, lean_object* v_otherState_558_){
_start:
{
uint8_t v_phase_boxed_559_; lean_object* v_res_560_; 
v_phase_boxed_559_ = lean_unbox(v_phase_554_);
v_res_560_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn(v_00_u03b2_553_, v_phase_boxed_559_, v_oldState_555_, v_newState_556_, v_x_557_, v_otherState_558_);
lean_dec(v_x_557_);
lean_dec_ref(v_newState_556_);
return v_res_560_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0(lean_object* v_00_u03b2_561_, lean_object* v_x_562_, lean_object* v_x_563_){
_start:
{
uint8_t v___x_564_; 
v___x_564_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg(v_x_562_, v_x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___boxed(lean_object* v_00_u03b2_565_, lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
uint8_t v_res_568_; lean_object* v_r_569_; 
v_res_568_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0(v_00_u03b2_565_, v_x_566_, v_x_567_);
lean_dec(v_x_567_);
v_r_569_ = lean_box(v_res_568_);
return v_r_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1(lean_object* v_00_u03b2_570_, lean_object* v_x_571_, lean_object* v_x_572_, lean_object* v_x_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_x_571_, v_x_572_, v_x_573_);
return v___x_574_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0(lean_object* v_00_u03b2_575_, lean_object* v_x_576_, size_t v_x_577_, lean_object* v_x_578_){
_start:
{
uint8_t v___x_579_; 
v___x_579_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg(v_x_576_, v_x_577_, v_x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___boxed(lean_object* v_00_u03b2_580_, lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v_x_583_){
_start:
{
size_t v_x_797__boxed_584_; uint8_t v_res_585_; lean_object* v_r_586_; 
v_x_797__boxed_584_ = lean_unbox_usize(v_x_582_);
lean_dec(v_x_582_);
v_res_585_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0(v_00_u03b2_580_, v_x_581_, v_x_797__boxed_584_, v_x_583_);
lean_dec(v_x_583_);
v_r_586_ = lean_box(v_res_585_);
return v_r_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2(lean_object* v_00_u03b2_587_, lean_object* v_x_588_, size_t v_x_589_, size_t v_x_590_, lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___redArg(v_x_588_, v_x_589_, v_x_590_, v_x_591_, v_x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_594_, lean_object* v_x_595_, lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_x_598_, lean_object* v_x_599_){
_start:
{
size_t v_x_808__boxed_600_; size_t v_x_809__boxed_601_; lean_object* v_res_602_; 
v_x_808__boxed_600_ = lean_unbox_usize(v_x_596_);
lean_dec(v_x_596_);
v_x_809__boxed_601_ = lean_unbox_usize(v_x_597_);
lean_dec(v_x_597_);
v_res_602_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2(v_00_u03b2_594_, v_x_595_, v_x_808__boxed_600_, v_x_809__boxed_601_, v_x_598_, v_x_599_);
return v_res_602_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_603_, lean_object* v_keys_604_, lean_object* v_vals_605_, lean_object* v_heq_606_, lean_object* v_i_607_, lean_object* v_k_608_){
_start:
{
uint8_t v___x_609_; 
v___x_609_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___redArg(v_keys_604_, v_i_607_, v_k_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_610_, lean_object* v_keys_611_, lean_object* v_vals_612_, lean_object* v_heq_613_, lean_object* v_i_614_, lean_object* v_k_615_){
_start:
{
uint8_t v_res_616_; lean_object* v_r_617_; 
v_res_616_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0_spec__1(v_00_u03b2_610_, v_keys_611_, v_vals_612_, v_heq_613_, v_i_614_, v_k_615_);
lean_dec(v_k_615_);
lean_dec_ref(v_vals_612_);
lean_dec_ref(v_keys_611_);
v_r_617_ = lean_box(v_res_616_);
return v_r_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_618_, lean_object* v_n_619_, lean_object* v_k_620_, lean_object* v_v_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4___redArg(v_n_619_, v_k_620_, v_v_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_623_, size_t v_depth_624_, lean_object* v_keys_625_, lean_object* v_vals_626_, lean_object* v_heq_627_, lean_object* v_i_628_, lean_object* v_entries_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___redArg(v_depth_624_, v_keys_625_, v_vals_626_, v_i_628_, v_entries_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_631_, lean_object* v_depth_632_, lean_object* v_keys_633_, lean_object* v_vals_634_, lean_object* v_heq_635_, lean_object* v_i_636_, lean_object* v_entries_637_){
_start:
{
size_t v_depth_boxed_638_; lean_object* v_res_639_; 
v_depth_boxed_638_ = lean_unbox_usize(v_depth_632_);
lean_dec(v_depth_632_);
v_res_639_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__5(v_00_u03b2_631_, v_depth_boxed_638_, v_keys_633_, v_vals_634_, v_heq_635_, v_i_636_, v_entries_637_);
lean_dec_ref(v_vals_634_);
lean_dec_ref(v_keys_633_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_640_, lean_object* v_x_641_, lean_object* v_x_642_, lean_object* v_x_643_, lean_object* v_x_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1_spec__2_spec__4_spec__5___redArg(v_x_641_, v_x_642_, v_x_643_, v_x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0(lean_object* v_count_646_, lean_object* v_x_647_, lean_object* v_x_648_){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_nat_add(v_count_646_, v___x_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0___boxed(lean_object* v_count_651_, lean_object* v_x_652_, lean_object* v_x_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___lam__0(v_count_651_, v_x_652_, v_x_653_);
lean_dec(v_x_653_);
lean_dec(v_x_652_);
lean_dec(v_count_651_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg(lean_object* v_state_659_){
_start:
{
lean_object* v___f_660_; lean_object* v___x_661_; lean_object* v_numEntries_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___f_660_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__0));
v___x_661_ = lean_unsigned_to_nat(0u);
v_numEntries_662_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_state_659_, v___f_660_, v___x_661_);
v___x_663_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___closed__2));
v___x_664_ = l_Nat_reprFast(v_numEntries_662_);
v___x_665_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
v___x_666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_663_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg___boxed(lean_object* v_state_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg(v_state_667_);
lean_dec_ref(v_state_667_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn(uint8_t v_pu_669_, lean_object* v_00_u03b2_670_, lean_object* v_state_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___redArg(v_state_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___boxed(lean_object* v_pu_673_, lean_object* v_00_u03b2_674_, lean_object* v_state_675_){
_start:
{
uint8_t v_pu_boxed_676_; lean_object* v_res_677_; 
v_pu_boxed_676_ = lean_unbox(v_pu_673_);
v_res_677_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn(v_pu_boxed_676_, v_00_u03b2_674_, v_state_675_);
lean_dec_ref(v_state_675_);
return v_res_677_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___redArg(lean_object* v_a_678_, lean_object* v_b_679_){
_start:
{
lean_object* v_toSignature_680_; lean_object* v_toSignature_681_; lean_object* v_name_682_; lean_object* v_name_683_; uint8_t v___x_684_; 
v_toSignature_680_ = lean_ctor_get(v_a_678_, 0);
v_toSignature_681_ = lean_ctor_get(v_b_679_, 0);
v_name_682_ = lean_ctor_get(v_toSignature_680_, 0);
v_name_683_ = lean_ctor_get(v_toSignature_681_, 0);
v___x_684_ = l_Lean_Name_quickLt(v_name_682_, v_name_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___redArg___boxed(lean_object* v_a_685_, lean_object* v_b_686_){
_start:
{
uint8_t v_res_687_; lean_object* v_r_688_; 
v_res_687_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___redArg(v_a_685_, v_b_686_);
lean_dec_ref(v_b_686_);
lean_dec_ref(v_a_685_);
v_r_688_ = lean_box(v_res_687_);
return v_r_688_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt(uint8_t v_pu_689_, lean_object* v_a_690_, lean_object* v_b_691_){
_start:
{
lean_object* v_toSignature_692_; lean_object* v_toSignature_693_; lean_object* v_name_694_; lean_object* v_name_695_; uint8_t v___x_696_; 
v_toSignature_692_ = lean_ctor_get(v_a_690_, 0);
v_toSignature_693_ = lean_ctor_get(v_b_691_, 0);
v_name_694_ = lean_ctor_get(v_toSignature_692_, 0);
v_name_695_ = lean_ctor_get(v_toSignature_693_, 0);
v___x_696_ = l_Lean_Name_quickLt(v_name_694_, v_name_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___boxed(lean_object* v_pu_697_, lean_object* v_a_698_, lean_object* v_b_699_){
_start:
{
uint8_t v_pu_boxed_700_; uint8_t v_res_701_; lean_object* v_r_702_; 
v_pu_boxed_700_ = lean_unbox(v_pu_697_);
v_res_701_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt(v_pu_boxed_700_, v_a_698_, v_b_699_);
lean_dec_ref(v_b_699_);
lean_dec_ref(v_a_698_);
v_r_702_ = lean_box(v_res_701_);
return v_r_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f(uint8_t v_pu_704_, lean_object* v_decls_705_, lean_object* v_declName_706_){
_start:
{
lean_object* v_tmpDecl_707_; lean_object* v_toSignature_708_; lean_object* v_value_709_; uint8_t v_recursive_710_; lean_object* v_inlineAttr_x3f_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_742_; 
v_tmpDecl_707_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v_pu_704_);
v_toSignature_708_ = lean_ctor_get(v_tmpDecl_707_, 0);
v_value_709_ = lean_ctor_get(v_tmpDecl_707_, 1);
v_recursive_710_ = lean_ctor_get_uint8(v_tmpDecl_707_, sizeof(void*)*3);
v_inlineAttr_x3f_711_ = lean_ctor_get(v_tmpDecl_707_, 2);
v_isSharedCheck_742_ = !lean_is_exclusive(v_tmpDecl_707_);
if (v_isSharedCheck_742_ == 0)
{
v___x_713_ = v_tmpDecl_707_;
v_isShared_714_ = v_isSharedCheck_742_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_inlineAttr_x3f_711_);
lean_inc(v_value_709_);
lean_inc(v_toSignature_708_);
lean_dec(v_tmpDecl_707_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_742_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v_levelParams_715_; lean_object* v_type_716_; lean_object* v_params_717_; uint8_t v_safe_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_740_; 
v_levelParams_715_ = lean_ctor_get(v_toSignature_708_, 1);
v_type_716_ = lean_ctor_get(v_toSignature_708_, 2);
v_params_717_ = lean_ctor_get(v_toSignature_708_, 3);
v_safe_718_ = lean_ctor_get_uint8(v_toSignature_708_, sizeof(void*)*4);
v_isSharedCheck_740_ = !lean_is_exclusive(v_toSignature_708_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; 
v_unused_741_ = lean_ctor_get(v_toSignature_708_, 0);
lean_dec(v_unused_741_);
v___x_720_ = v_toSignature_708_;
v_isShared_721_ = v_isSharedCheck_740_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_params_717_);
lean_inc(v_type_716_);
lean_inc(v_levelParams_715_);
lean_dec(v_toSignature_708_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_740_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = lean_array_get_size(v_decls_705_);
v___x_724_ = lean_nat_dec_lt(v___x_722_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
lean_del_object(v___x_720_);
lean_dec_ref(v_params_717_);
lean_dec_ref(v_type_716_);
lean_dec(v_levelParams_715_);
lean_del_object(v___x_713_);
lean_dec(v_inlineAttr_x3f_711_);
lean_dec_ref(v_value_709_);
lean_dec(v_declName_706_);
v___x_725_ = lean_box(0);
return v___x_725_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_726_ = lean_unsigned_to_nat(1u);
v___x_727_ = lean_nat_sub(v___x_723_, v___x_726_);
v___x_728_ = lean_nat_dec_le(v___x_722_, v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; 
lean_dec(v___x_727_);
lean_del_object(v___x_720_);
lean_dec_ref(v_params_717_);
lean_dec_ref(v_type_716_);
lean_dec(v_levelParams_715_);
lean_del_object(v___x_713_);
lean_dec(v_inlineAttr_x3f_711_);
lean_dec_ref(v_value_709_);
lean_dec(v_declName_706_);
v___x_729_ = lean_box(0);
return v___x_729_;
}
else
{
lean_object* v___x_731_; 
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v_declName_706_);
v___x_731_ = v___x_720_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_declName_706_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_levelParams_715_);
lean_ctor_set(v_reuseFailAlloc_739_, 2, v_type_716_);
lean_ctor_set(v_reuseFailAlloc_739_, 3, v_params_717_);
lean_ctor_set_uint8(v_reuseFailAlloc_739_, sizeof(void*)*4, v_safe_718_);
v___x_731_ = v_reuseFailAlloc_739_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v_tmpDecl_733_; 
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_731_);
v_tmpDecl_733_ = v___x_713_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_value_709_);
lean_ctor_set(v_reuseFailAlloc_738_, 2, v_inlineAttr_x3f_711_);
lean_ctor_set_uint8(v_reuseFailAlloc_738_, sizeof(void*)*3, v_recursive_710_);
v_tmpDecl_733_ = v_reuseFailAlloc_738_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_734_ = lean_box(v_pu_704_);
v___x_735_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_declLt___boxed), 3, 1);
lean_closure_set(v___x_735_, 0, v___x_734_);
v___x_736_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___closed__0));
v___x_737_ = l_Array_binSearchAux___redArg(v___x_735_, v___x_736_, v_decls_705_, v_tmpDecl_733_, v___x_722_, v___x_727_);
return v___x_737_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f___boxed(lean_object* v_pu_743_, lean_object* v_decls_744_, lean_object* v_declName_745_){
_start:
{
uint8_t v_pu_boxed_746_; lean_object* v_res_747_; 
v_pu_boxed_746_ = lean_unbox(v_pu_743_);
v_res_747_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findDeclAtSorted_x3f(v_pu_boxed_746_, v_decls_744_, v_declName_745_);
lean_dec_ref(v_decls_744_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0(lean_object* v_x_751_, lean_object* v___y_752_){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__1));
v___x_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___boxed(lean_object* v_x_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0(v_x_756_, v___y_757_);
lean_dec_ref(v___y_757_);
lean_dec_ref(v_x_756_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__1(lean_object* v_s_760_, lean_object* v_x_761_){
_start:
{
lean_inc_ref(v_s_760_);
return v_s_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__1___boxed(lean_object* v_s_762_, lean_object* v_x_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__1(v_s_762_, v_x_763_);
lean_dec_ref(v_x_763_);
lean_dec_ref(v_s_762_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2(lean_object* v_x_767_, lean_object* v_x_768_, uint8_t v_x_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0));
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___boxed(lean_object* v_x_771_, lean_object* v_x_772_, lean_object* v_x_773_){
_start:
{
uint8_t v_x_92__boxed_774_; lean_object* v_res_775_; 
v_x_92__boxed_774_ = lean_unbox(v_x_773_);
v_res_775_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2(v_x_771_, v_x_772_, v_x_92__boxed_774_);
lean_dec_ref(v_x_772_);
lean_dec_ref(v_x_771_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__3(lean_object* v_x_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = lean_box(0);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__3___boxed(lean_object* v_x_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__3(v_x_778_);
lean_dec_ref(v_x_778_);
return v_res_779_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__4(void){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_784_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5(void){
_start:
{
lean_object* v___f_785_; lean_object* v___f_786_; lean_object* v___f_787_; lean_object* v___f_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___f_785_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__3));
v___f_786_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__2));
v___f_787_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__1));
v___f_788_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__0));
v___x_789_ = lean_box(0);
v___x_790_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__4, &l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__4_once, _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__4);
v___x_791_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v___x_789_);
lean_ctor_set(v___x_791_, 2, v___f_788_);
lean_ctor_set(v___x_791_, 3, v___f_787_);
lean_ctor_set(v___x_791_, 4, v___f_786_);
lean_ctor_set(v___x_791_, 5, v___f_785_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1(uint8_t v_pu_792_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5, &l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5_once, _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___boxed(lean_object* v_pu_794_){
_start:
{
uint8_t v_pu_boxed_795_; lean_object* v_res_796_; 
v_pu_boxed_795_ = lean_unbox(v_pu_794_);
v_res_796_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1(v_pu_boxed_795_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt(uint8_t v_pu_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5, &l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5_once, _init_l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___closed__5);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedDeclExt___boxed(lean_object* v_pu_799_){
_start:
{
uint8_t v_pu_boxed_800_; lean_object* v_res_801_; 
v_pu_boxed_800_ = lean_unbox(v_pu_799_);
v_res_801_ = l_Lean_Compiler_LCNF_instInhabitedDeclExt(v_pu_boxed_800_);
return v_res_801_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__10));
v___x_829_ = l_Lean_mkAtom(v___x_828_);
return v___x_829_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_830_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__12);
v___x_831_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5));
v___x_832_ = lean_array_push(v___x_831_, v___x_830_);
return v___x_832_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__17));
v___x_842_ = l_Lean_mkAtom(v___x_841_);
return v___x_842_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_843_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__18);
v___x_844_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5));
v___x_845_ = lean_array_push(v___x_844_, v___x_843_);
return v___x_845_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_846_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__19);
v___x_847_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__16));
v___x_848_ = lean_box(2);
v___x_849_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
lean_ctor_set(v___x_849_, 1, v___x_847_);
lean_ctor_set(v___x_849_, 2, v___x_846_);
return v___x_849_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_850_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__20);
v___x_851_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__13);
v___x_852_ = lean_array_push(v___x_851_, v___x_850_);
return v___x_852_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_853_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__21);
v___x_854_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__11));
v___x_855_ = lean_box(2);
v___x_856_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v___x_854_);
lean_ctor_set(v___x_856_, 2, v___x_853_);
return v___x_856_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_857_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__22);
v___x_858_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5));
v___x_859_ = lean_array_push(v___x_858_, v___x_857_);
return v___x_859_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_860_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__23);
v___x_861_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__9));
v___x_862_ = lean_box(2);
v___x_863_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
lean_ctor_set(v___x_863_, 1, v___x_861_);
lean_ctor_set(v___x_863_, 2, v___x_860_);
return v___x_863_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_864_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__24);
v___x_865_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5));
v___x_866_ = lean_array_push(v___x_865_, v___x_864_);
return v___x_866_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_867_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__25);
v___x_868_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__7));
v___x_869_ = lean_box(2);
v___x_870_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v___x_868_);
lean_ctor_set(v___x_870_, 2, v___x_867_);
return v___x_870_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_871_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__26);
v___x_872_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__5));
v___x_873_ = lean_array_push(v___x_872_, v___x_871_);
return v___x_873_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_874_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__27);
v___x_875_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__4));
v___x_876_ = lean_box(2);
v___x_877_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
lean_ctor_set(v___x_877_, 1, v___x_875_);
lean_ctor_set(v___x_877_, 2, v___x_874_);
return v___x_877_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1(void){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__0(lean_object* v_s_879_, lean_object* v_decl_880_){
_start:
{
lean_object* v_toSignature_881_; lean_object* v_name_882_; lean_object* v___x_883_; 
v_toSignature_881_ = lean_ctor_get(v_decl_880_, 0);
v_name_882_ = lean_ctor_get(v_toSignature_881_, 0);
lean_inc(v_name_882_);
v___x_883_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_s_879_, v_name_882_, v_decl_880_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__1(lean_object* v_x_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0));
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__1___boxed(lean_object* v_x_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__1(v_x_886_);
lean_dec_ref(v_x_886_);
return v_res_887_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_mkDeclExt___lam__2(lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v_toSignature_890_; lean_object* v_toSignature_891_; lean_object* v_name_892_; lean_object* v_name_893_; uint8_t v___x_894_; 
v_toSignature_890_ = lean_ctor_get(v___y_888_, 0);
v_toSignature_891_ = lean_ctor_get(v___y_889_, 0);
v_name_892_ = lean_ctor_get(v_toSignature_890_, 0);
v_name_893_ = lean_ctor_get(v_toSignature_891_, 0);
v___x_894_ = l_Lean_Name_quickLt(v_name_892_, v_name_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__2___boxed(lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
uint8_t v_res_897_; lean_object* v_r_898_; 
v_res_897_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__2(v___y_895_, v___y_896_);
lean_dec_ref(v___y_896_);
lean_dec_ref(v___y_895_);
v_r_898_ = lean_box(v_res_897_);
return v_r_898_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(lean_object* v_env_904_, uint8_t v_phase_905_, lean_object* v_as_906_, size_t v_i_907_, size_t v_stop_908_, lean_object* v_b_909_){
_start:
{
lean_object* v___y_911_; uint8_t v___x_915_; 
v___x_915_ = lean_usize_dec_eq(v_i_907_, v_stop_908_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v_toSignature_917_; uint8_t v_recursive_918_; lean_object* v_inlineAttr_x3f_919_; lean_object* v_name_920_; uint8_t v___x_921_; 
v___x_916_ = lean_array_uget(v_as_906_, v_i_907_);
v_toSignature_917_ = lean_ctor_get(v___x_916_, 0);
v_recursive_918_ = lean_ctor_get_uint8(v___x_916_, sizeof(void*)*3);
v_inlineAttr_x3f_919_ = lean_ctor_get(v___x_916_, 2);
v_name_920_ = lean_ctor_get(v_toSignature_917_, 0);
lean_inc_ref(v_env_904_);
v___x_921_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_904_, v_name_920_);
if (v___x_921_ == 0)
{
lean_dec(v___x_916_);
v___y_911_ = v_b_909_;
goto v___jp_910_;
}
else
{
uint8_t v___x_922_; 
lean_inc_ref(v_env_904_);
v___x_922_ = l_Lean_Compiler_LCNF_isDeclTransparent(v_env_904_, v_phase_905_, v_name_920_);
if (v___x_922_ == 0)
{
lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_931_; 
lean_inc(v_inlineAttr_x3f_919_);
lean_inc_ref(v_toSignature_917_);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_931_ == 0)
{
lean_object* v_unused_932_; lean_object* v_unused_933_; lean_object* v_unused_934_; 
v_unused_932_ = lean_ctor_get(v___x_916_, 2);
lean_dec(v_unused_932_);
v_unused_933_ = lean_ctor_get(v___x_916_, 1);
lean_dec(v_unused_933_);
v_unused_934_ = lean_ctor_get(v___x_916_, 0);
lean_dec(v_unused_934_);
v___x_924_ = v___x_916_;
v_isShared_925_ = v_isSharedCheck_931_;
goto v_resetjp_923_;
}
else
{
lean_dec(v___x_916_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_931_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_926_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___closed__1));
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 1, v___x_926_);
v___x_928_ = v___x_924_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_toSignature_917_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_930_, 2, v_inlineAttr_x3f_919_);
lean_ctor_set_uint8(v_reuseFailAlloc_930_, sizeof(void*)*3, v_recursive_918_);
v___x_928_ = v_reuseFailAlloc_930_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_929_; 
v___x_929_ = lean_array_push(v_b_909_, v___x_928_);
v___y_911_ = v___x_929_;
goto v___jp_910_;
}
}
}
else
{
lean_object* v___x_935_; 
v___x_935_ = lean_array_push(v_b_909_, v___x_916_);
v___y_911_ = v___x_935_;
goto v___jp_910_;
}
}
}
else
{
lean_dec_ref(v_env_904_);
return v_b_909_;
}
v___jp_910_:
{
size_t v___x_912_; size_t v___x_913_; 
v___x_912_ = ((size_t)1ULL);
v___x_913_ = lean_usize_add(v_i_907_, v___x_912_);
v_i_907_ = v___x_913_;
v_b_909_ = v___y_911_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg___boxed(lean_object* v_env_936_, lean_object* v_phase_937_, lean_object* v_as_938_, lean_object* v_i_939_, lean_object* v_stop_940_, lean_object* v_b_941_){
_start:
{
uint8_t v_phase_boxed_942_; size_t v_i_boxed_943_; size_t v_stop_boxed_944_; lean_object* v_res_945_; 
v_phase_boxed_942_ = lean_unbox(v_phase_937_);
v_i_boxed_943_ = lean_unbox_usize(v_i_939_);
lean_dec(v_i_939_);
v_stop_boxed_944_ = lean_unbox_usize(v_stop_940_);
lean_dec(v_stop_940_);
v_res_945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(v_env_936_, v_phase_boxed_942_, v_as_938_, v_i_boxed_943_, v_stop_boxed_944_, v_b_941_);
lean_dec_ref(v_as_938_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0(lean_object* v_env_946_, uint8_t v_phase_947_, uint8_t v___x_948_, lean_object* v_as_949_, lean_object* v_start_950_, lean_object* v_stop_951_){
_start:
{
lean_object* v___x_952_; uint8_t v___x_953_; 
v___x_952_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__2___closed__0));
v___x_953_ = lean_nat_dec_lt(v_start_950_, v_stop_951_);
if (v___x_953_ == 0)
{
lean_dec_ref(v_env_946_);
return v___x_952_;
}
else
{
lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_954_ = lean_array_get_size(v_as_949_);
v___x_955_ = lean_nat_dec_le(v_stop_951_, v___x_954_);
if (v___x_955_ == 0)
{
uint8_t v___x_956_; 
v___x_956_ = lean_nat_dec_lt(v_start_950_, v___x_954_);
if (v___x_956_ == 0)
{
lean_dec_ref(v_env_946_);
return v___x_952_;
}
else
{
size_t v___x_957_; size_t v___x_958_; lean_object* v___x_959_; 
v___x_957_ = lean_usize_of_nat(v_start_950_);
v___x_958_ = lean_usize_of_nat(v___x_954_);
v___x_959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(v_env_946_, v_phase_947_, v_as_949_, v___x_957_, v___x_958_, v___x_952_);
return v___x_959_;
}
}
else
{
size_t v___x_960_; size_t v___x_961_; lean_object* v___x_962_; 
v___x_960_ = lean_usize_of_nat(v_start_950_);
v___x_961_ = lean_usize_of_nat(v_stop_951_);
v___x_962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(v_env_946_, v_phase_947_, v_as_949_, v___x_960_, v___x_961_, v___x_952_);
return v___x_962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0___boxed(lean_object* v_env_963_, lean_object* v_phase_964_, lean_object* v___x_965_, lean_object* v_as_966_, lean_object* v_start_967_, lean_object* v_stop_968_){
_start:
{
uint8_t v_phase_boxed_969_; uint8_t v___x_1219__boxed_970_; lean_object* v_res_971_; 
v_phase_boxed_969_ = lean_unbox(v_phase_964_);
v___x_1219__boxed_970_ = lean_unbox(v___x_965_);
v_res_971_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0(v_env_963_, v_phase_boxed_969_, v___x_1219__boxed_970_, v_as_966_, v_start_967_, v_stop_968_);
lean_dec(v_stop_968_);
lean_dec(v_start_967_);
lean_dec_ref(v_as_966_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__3(lean_object* v___f_972_, uint8_t v_phase_973_, lean_object* v_env_974_, lean_object* v_s_975_, uint8_t v_level_976_){
_start:
{
lean_object* v_entries_977_; uint8_t v___x_978_; uint8_t v___x_979_; 
v_entries_977_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(v_s_975_, v___f_972_);
v___x_978_ = 2;
v___x_979_ = l_Lean_instDecidableEqOLeanLevel(v_level_976_, v___x_978_);
if (v___x_979_ == 0)
{
uint8_t v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v_entries_983_; 
v___x_980_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_973_);
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = lean_array_get_size(v_entries_977_);
v_entries_983_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0(v_env_974_, v_phase_973_, v___x_980_, v_entries_977_, v___x_981_, v___x_982_);
lean_dec_ref(v_entries_977_);
return v_entries_983_;
}
else
{
lean_dec_ref(v_env_974_);
return v_entries_977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__3___boxed(lean_object* v___f_984_, lean_object* v_phase_985_, lean_object* v_env_986_, lean_object* v_s_987_, lean_object* v_level_988_){
_start:
{
uint8_t v_phase_boxed_989_; uint8_t v_level_boxed_990_; lean_object* v_res_991_; 
v_phase_boxed_989_ = lean_unbox(v_phase_985_);
v_level_boxed_990_ = lean_unbox(v_level_988_);
v_res_991_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__3(v___f_984_, v_phase_boxed_989_, v_env_986_, v_s_987_, v_level_boxed_990_);
lean_dec_ref(v_s_987_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__4(lean_object* v___x_992_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__4___boxed(lean_object* v___x_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__4(v___x_995_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__5(lean_object* v___x_998_, lean_object* v_x_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1002_, 0, v___x_998_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___lam__5___boxed(lean_object* v___x_1003_, lean_object* v_x_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__5(v___x_1003_, v_x_1004_, v___y_1005_);
lean_dec_ref(v___y_1005_);
lean_dec_ref(v_x_1004_);
return v_res_1007_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__3(void){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__4(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__3, &l_Lean_Compiler_LCNF_mkDeclExt___closed__3_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__3);
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__5(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___f_1015_; 
v___x_1014_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__4, &l_Lean_Compiler_LCNF_mkDeclExt___closed__4_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__4);
v___f_1015_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkDeclExt___lam__4___boxed), 2, 1);
lean_closure_set(v___f_1015_, 0, v___x_1014_);
return v___f_1015_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__6(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___f_1017_; 
v___x_1016_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__4, &l_Lean_Compiler_LCNF_mkDeclExt___closed__4_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__4);
v___f_1017_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkDeclExt___lam__5___boxed), 4, 1);
lean_closure_set(v___f_1017_, 0, v___x_1016_);
return v___f_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt(uint8_t v_phase_1018_, lean_object* v_name_1019_){
_start:
{
lean_object* v___f_1021_; lean_object* v___f_1022_; lean_object* v___f_1023_; lean_object* v___x_1024_; lean_object* v___f_1025_; lean_object* v___f_1026_; lean_object* v___f_1027_; uint8_t v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___f_1021_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___closed__0));
v___f_1022_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___closed__1));
v___f_1023_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkDeclExt___closed__2));
v___x_1024_ = lean_box(v_phase_1018_);
v___f_1025_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkDeclExt___lam__3___boxed), 5, 2);
lean_closure_set(v___f_1025_, 0, v___f_1023_);
lean_closure_set(v___f_1025_, 1, v___x_1024_);
v___f_1026_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__5, &l_Lean_Compiler_LCNF_mkDeclExt___closed__5_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__5);
v___f_1027_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__6, &l_Lean_Compiler_LCNF_mkDeclExt___closed__6_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__6);
v___x_1028_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_1018_);
v___x_1029_ = lean_box(v___x_1028_);
v___x_1030_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___boxed), 3, 2);
lean_closure_set(v___x_1030_, 0, v___x_1029_);
lean_closure_set(v___x_1030_, 1, lean_box(0));
v___x_1031_ = lean_box(0);
v___x_1032_ = lean_box(v_phase_1018_);
v___x_1033_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___boxed), 6, 2);
lean_closure_set(v___x_1033_, 0, lean_box(0));
lean_closure_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
v___x_1035_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1035_, 0, v_name_1019_);
lean_ctor_set(v___x_1035_, 1, v___f_1026_);
lean_ctor_set(v___x_1035_, 2, v___f_1027_);
lean_ctor_set(v___x_1035_, 3, v___f_1021_);
lean_ctor_set(v___x_1035_, 4, v___f_1025_);
lean_ctor_set(v___x_1035_, 5, v___x_1030_);
lean_ctor_set(v___x_1035_, 6, v___x_1031_);
lean_ctor_set(v___x_1035_, 7, v___x_1034_);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
lean_ctor_set(v___x_1036_, 1, v___f_1022_);
v___x_1037_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkDeclExt___boxed(lean_object* v_phase_1038_, lean_object* v_name_1039_, lean_object* v_a_1040_){
_start:
{
uint8_t v_phase_boxed_1041_; lean_object* v_res_1042_; 
v_phase_boxed_1041_ = lean_unbox(v_phase_1038_);
v_res_1042_ = l_Lean_Compiler_LCNF_mkDeclExt(v_phase_boxed_1041_, v_name_1039_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0(lean_object* v_env_1043_, uint8_t v_phase_1044_, uint8_t v___x_1045_, lean_object* v_as_1046_, size_t v_i_1047_, size_t v_stop_1048_, lean_object* v_b_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___redArg(v_env_1043_, v_phase_1044_, v_as_1046_, v_i_1047_, v_stop_1048_, v_b_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0___boxed(lean_object* v_env_1051_, lean_object* v_phase_1052_, lean_object* v___x_1053_, lean_object* v_as_1054_, lean_object* v_i_1055_, lean_object* v_stop_1056_, lean_object* v_b_1057_){
_start:
{
uint8_t v_phase_boxed_1058_; uint8_t v___x_1347__boxed_1059_; size_t v_i_boxed_1060_; size_t v_stop_boxed_1061_; lean_object* v_res_1062_; 
v_phase_boxed_1058_ = lean_unbox(v_phase_1052_);
v___x_1347__boxed_1059_ = lean_unbox(v___x_1053_);
v_i_boxed_1060_ = lean_unbox_usize(v_i_1055_);
lean_dec(v_i_1055_);
v_stop_boxed_1061_ = lean_unbox_usize(v_stop_1056_);
lean_dec(v_stop_1056_);
v_res_1062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkDeclExt_spec__0_spec__0(v_env_1051_, v_phase_boxed_1058_, v___x_1347__boxed_1059_, v_as_1054_, v_i_boxed_1060_, v_stop_boxed_1061_, v_b_1057_);
lean_dec_ref(v_as_1054_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1072_ = 0;
v___x_1073_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_));
v___x_1074_ = l_Lean_Compiler_LCNF_mkDeclExt(v___x_1072_, v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2____boxed(lean_object* v_a_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_();
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1084_ = 1;
v___x_1085_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_));
v___x_1086_ = l_Lean_Compiler_LCNF_mkDeclExt(v___x_1084_, v___x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2____boxed(lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_();
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___f_1095_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___closed__5, &l_Lean_Compiler_LCNF_mkDeclExt___closed__5_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___closed__5);
v___x_1096_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_));
v___x_1097_ = lean_box(0);
v___x_1098_ = l_Lean_registerEnvExtension___redArg(v___f_1095_, v___x_1096_, v___x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2____boxed(lean_object* v_a_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_();
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__0(lean_object* v_x_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedDeclExt___aux__1___lam__0___closed__1));
v___x_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__0___boxed(lean_object* v_x_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__0(v_x_1106_, v___y_1107_);
lean_dec_ref(v___y_1107_);
lean_dec_ref(v_x_1106_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__1(lean_object* v_s_1110_, lean_object* v_x_1111_){
_start:
{
lean_inc_ref(v_s_1110_);
return v_s_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__1___boxed(lean_object* v_s_1112_, lean_object* v_x_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__1(v_s_1112_, v_x_1113_);
lean_dec_ref(v_x_1113_);
lean_dec_ref(v_s_1112_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2(lean_object* v_x_1117_, lean_object* v_x_1118_, uint8_t v_x_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0));
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___boxed(lean_object* v_x_1121_, lean_object* v_x_1122_, lean_object* v_x_1123_){
_start:
{
uint8_t v_x_87__boxed_1124_; lean_object* v_res_1125_; 
v_x_87__boxed_1124_ = lean_unbox(v_x_1123_);
v_res_1125_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2(v_x_1121_, v_x_1122_, v_x_87__boxed_1124_);
lean_dec_ref(v_x_1122_);
lean_dec_ref(v_x_1121_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__3(lean_object* v_x_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_box(0);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__3___boxed(lean_object* v_x_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__3(v_x_1128_);
lean_dec_ref(v_x_1128_);
return v_res_1129_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__4(void){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1134_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5(void){
_start:
{
lean_object* v___f_1135_; lean_object* v___f_1136_; lean_object* v___f_1137_; lean_object* v___f_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___f_1135_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__3));
v___f_1136_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__2));
v___f_1137_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__1));
v___f_1138_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__0));
v___x_1139_ = lean_box(0);
v___x_1140_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__4, &l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__4_once, _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__4);
v___x_1141_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
lean_ctor_set(v___x_1141_, 1, v___x_1139_);
lean_ctor_set(v___x_1141_, 2, v___f_1138_);
lean_ctor_set(v___x_1141_, 3, v___f_1137_);
lean_ctor_set(v___x_1141_, 4, v___f_1136_);
lean_ctor_set(v___x_1141_, 5, v___f_1135_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1(uint8_t v_pu_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5, &l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5_once, _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___boxed(lean_object* v_pu_1144_){
_start:
{
uint8_t v_pu_boxed_1145_; lean_object* v_res_1146_; 
v_pu_boxed_1145_ = lean_unbox(v_pu_1144_);
v_res_1146_ = l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1(v_pu_boxed_1145_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt(uint8_t v_pu_1147_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = lean_obj_once(&l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5, &l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5_once, _init_l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___closed__5);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_instInhabitedSigExt___boxed(lean_object* v_pu_1149_){
_start:
{
uint8_t v_pu_boxed_1150_; lean_object* v_res_1151_; 
v_pu_boxed_1150_ = lean_unbox(v_pu_1149_);
v_res_1151_ = l_Lean_Compiler_LCNF_instInhabitedSigExt(v_pu_boxed_1150_);
return v_res_1151_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___redArg(lean_object* v_a_1152_, lean_object* v_b_1153_){
_start:
{
lean_object* v_name_1154_; lean_object* v_name_1155_; uint8_t v___x_1156_; 
v_name_1154_ = lean_ctor_get(v_a_1152_, 0);
v_name_1155_ = lean_ctor_get(v_b_1153_, 0);
v___x_1156_ = l_Lean_Name_quickLt(v_name_1154_, v_name_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___redArg___boxed(lean_object* v_a_1157_, lean_object* v_b_1158_){
_start:
{
uint8_t v_res_1159_; lean_object* v_r_1160_; 
v_res_1159_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___redArg(v_a_1157_, v_b_1158_);
lean_dec_ref(v_b_1158_);
lean_dec_ref(v_a_1157_);
v_r_1160_ = lean_box(v_res_1159_);
return v_r_1160_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt(uint8_t v_pu_1161_, lean_object* v_a_1162_, lean_object* v_b_1163_){
_start:
{
lean_object* v_name_1164_; lean_object* v_name_1165_; uint8_t v___x_1166_; 
v_name_1164_ = lean_ctor_get(v_a_1162_, 0);
v_name_1165_ = lean_ctor_get(v_b_1163_, 0);
v___x_1166_ = l_Lean_Name_quickLt(v_name_1164_, v_name_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___boxed(lean_object* v_pu_1167_, lean_object* v_a_1168_, lean_object* v_b_1169_){
_start:
{
uint8_t v_pu_boxed_1170_; uint8_t v_res_1171_; lean_object* v_r_1172_; 
v_pu_boxed_1170_ = lean_unbox(v_pu_1167_);
v_res_1171_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt(v_pu_boxed_1170_, v_a_1168_, v_b_1169_);
lean_dec_ref(v_b_1169_);
lean_dec_ref(v_a_1168_);
v_r_1172_ = lean_box(v_res_1171_);
return v_r_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f(uint8_t v_pu_1174_, lean_object* v_sigs_1175_, lean_object* v_declName_1176_){
_start:
{
lean_object* v_tmpSig_1177_; lean_object* v_levelParams_1178_; lean_object* v_type_1179_; lean_object* v_params_1180_; uint8_t v_safe_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1200_; 
v_tmpSig_1177_ = l_Lean_Compiler_LCNF_instInhabitedSignature_default(v_pu_1174_);
v_levelParams_1178_ = lean_ctor_get(v_tmpSig_1177_, 1);
v_type_1179_ = lean_ctor_get(v_tmpSig_1177_, 2);
v_params_1180_ = lean_ctor_get(v_tmpSig_1177_, 3);
v_safe_1181_ = lean_ctor_get_uint8(v_tmpSig_1177_, sizeof(void*)*4);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_tmpSig_1177_);
if (v_isSharedCheck_1200_ == 0)
{
lean_object* v_unused_1201_; 
v_unused_1201_ = lean_ctor_get(v_tmpSig_1177_, 0);
lean_dec(v_unused_1201_);
v___x_1183_ = v_tmpSig_1177_;
v_isShared_1184_ = v_isSharedCheck_1200_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_params_1180_);
lean_inc(v_type_1179_);
lean_inc(v_levelParams_1178_);
lean_dec(v_tmpSig_1177_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1200_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; 
v___x_1185_ = lean_unsigned_to_nat(0u);
v___x_1186_ = lean_array_get_size(v_sigs_1175_);
v___x_1187_ = lean_nat_dec_lt(v___x_1185_, v___x_1186_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; 
lean_del_object(v___x_1183_);
lean_dec_ref(v_params_1180_);
lean_dec_ref(v_type_1179_);
lean_dec(v_levelParams_1178_);
lean_dec(v_declName_1176_);
v___x_1188_ = lean_box(0);
return v___x_1188_;
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1189_ = lean_unsigned_to_nat(1u);
v___x_1190_ = lean_nat_sub(v___x_1186_, v___x_1189_);
v___x_1191_ = lean_nat_dec_le(v___x_1185_, v___x_1190_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; 
lean_dec(v___x_1190_);
lean_del_object(v___x_1183_);
lean_dec_ref(v_params_1180_);
lean_dec_ref(v_type_1179_);
lean_dec(v_levelParams_1178_);
lean_dec(v_declName_1176_);
v___x_1192_ = lean_box(0);
return v___x_1192_;
}
else
{
lean_object* v_tmpSig_1194_; 
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v_declName_1176_);
v_tmpSig_1194_ = v___x_1183_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_declName_1176_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_levelParams_1178_);
lean_ctor_set(v_reuseFailAlloc_1199_, 2, v_type_1179_);
lean_ctor_set(v_reuseFailAlloc_1199_, 3, v_params_1180_);
lean_ctor_set_uint8(v_reuseFailAlloc_1199_, sizeof(void*)*4, v_safe_1181_);
v_tmpSig_1194_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1195_ = lean_box(v_pu_1174_);
v___x_1196_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sigLt___boxed), 3, 1);
lean_closure_set(v___x_1196_, 0, v___x_1195_);
v___x_1197_ = ((lean_object*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___closed__0));
v___x_1198_ = l_Array_binSearchAux___redArg(v___x_1196_, v___x_1197_, v_sigs_1175_, v_tmpSig_1194_, v___x_1185_, v___x_1190_);
return v___x_1198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f___boxed(lean_object* v_pu_1202_, lean_object* v_sigs_1203_, lean_object* v_declName_1204_){
_start:
{
uint8_t v_pu_boxed_1205_; lean_object* v_res_1206_; 
v_pu_boxed_1205_ = lean_unbox(v_pu_1202_);
v_res_1206_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_findSigAtSorted_x3f(v_pu_boxed_1205_, v_sigs_1203_, v_declName_1204_);
lean_dec_ref(v_sigs_1203_);
return v_res_1206_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkSigDeclExt___auto__1(void){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28, &l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28_once, _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1___closed__28);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__0(lean_object* v_s_1208_, lean_object* v_sig_1209_){
_start:
{
lean_object* v_name_1210_; lean_object* v___x_1211_; 
v_name_1210_ = lean_ctor_get(v_sig_1209_, 0);
lean_inc(v_name_1210_);
v___x_1211_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_s_1208_, v_name_1210_, v_sig_1209_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1(lean_object* v_x_1212_){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0));
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1___boxed(lean_object* v_x_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__1(v_x_1214_);
lean_dec_ref(v_x_1214_);
return v_res_1215_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_name_1218_; lean_object* v_name_1219_; uint8_t v___x_1220_; 
v_name_1218_ = lean_ctor_get(v___y_1216_, 0);
v_name_1219_ = lean_ctor_get(v___y_1217_, 0);
v___x_1220_ = l_Lean_Name_quickLt(v_name_1218_, v_name_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2___boxed(lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
uint8_t v_res_1223_; lean_object* v_r_1224_; 
v_res_1223_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(v___y_1221_, v___y_1222_);
lean_dec_ref(v___y_1222_);
lean_dec_ref(v___y_1221_);
v_r_1224_ = lean_box(v_res_1223_);
return v_r_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(lean_object* v_env_1225_, lean_object* v_as_1226_, size_t v_i_1227_, size_t v_stop_1228_, lean_object* v_b_1229_){
_start:
{
lean_object* v___y_1231_; uint8_t v___x_1235_; 
v___x_1235_ = lean_usize_dec_eq(v_i_1227_, v_stop_1228_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; lean_object* v_name_1237_; uint8_t v___x_1238_; 
v___x_1236_ = lean_array_uget_borrowed(v_as_1226_, v_i_1227_);
v_name_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc_ref(v_env_1225_);
v___x_1238_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_1225_, v_name_1237_);
if (v___x_1238_ == 0)
{
v___y_1231_ = v_b_1229_;
goto v___jp_1230_;
}
else
{
lean_object* v___x_1239_; 
lean_inc(v___x_1236_);
v___x_1239_ = lean_array_push(v_b_1229_, v___x_1236_);
v___y_1231_ = v___x_1239_;
goto v___jp_1230_;
}
}
else
{
lean_dec_ref(v_env_1225_);
return v_b_1229_;
}
v___jp_1230_:
{
size_t v___x_1232_; size_t v___x_1233_; 
v___x_1232_ = ((size_t)1ULL);
v___x_1233_ = lean_usize_add(v_i_1227_, v___x_1232_);
v_i_1227_ = v___x_1233_;
v_b_1229_ = v___y_1231_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0___boxed(lean_object* v_env_1240_, lean_object* v_as_1241_, lean_object* v_i_1242_, lean_object* v_stop_1243_, lean_object* v_b_1244_){
_start:
{
size_t v_i_boxed_1245_; size_t v_stop_boxed_1246_; lean_object* v_res_1247_; 
v_i_boxed_1245_ = lean_unbox_usize(v_i_1242_);
lean_dec(v_i_1242_);
v_stop_boxed_1246_ = lean_unbox_usize(v_stop_1243_);
lean_dec(v_stop_1243_);
v_res_1247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(v_env_1240_, v_as_1241_, v_i_boxed_1245_, v_stop_boxed_1246_, v_b_1244_);
lean_dec_ref(v_as_1241_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0(lean_object* v_env_1248_, lean_object* v_as_1249_, lean_object* v_start_1250_, lean_object* v_stop_1251_){
_start:
{
lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = ((lean_object*)(l_Lean_Compiler_LCNF_instInhabitedSigExt___aux__1___lam__2___closed__0));
v___x_1253_ = lean_nat_dec_lt(v_start_1250_, v_stop_1251_);
if (v___x_1253_ == 0)
{
lean_dec_ref(v_env_1248_);
return v___x_1252_;
}
else
{
lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = lean_array_get_size(v_as_1249_);
v___x_1255_ = lean_nat_dec_le(v_stop_1251_, v___x_1254_);
if (v___x_1255_ == 0)
{
uint8_t v___x_1256_; 
v___x_1256_ = lean_nat_dec_lt(v_start_1250_, v___x_1254_);
if (v___x_1256_ == 0)
{
lean_dec_ref(v_env_1248_);
return v___x_1252_;
}
else
{
size_t v___x_1257_; size_t v___x_1258_; lean_object* v___x_1259_; 
v___x_1257_ = lean_usize_of_nat(v_start_1250_);
v___x_1258_ = lean_usize_of_nat(v___x_1254_);
v___x_1259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(v_env_1248_, v_as_1249_, v___x_1257_, v___x_1258_, v___x_1252_);
return v___x_1259_;
}
}
else
{
size_t v___x_1260_; size_t v___x_1261_; lean_object* v___x_1262_; 
v___x_1260_ = lean_usize_of_nat(v_start_1250_);
v___x_1261_ = lean_usize_of_nat(v_stop_1251_);
v___x_1262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0_spec__0(v_env_1248_, v_as_1249_, v___x_1260_, v___x_1261_, v___x_1252_);
return v___x_1262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0___boxed(lean_object* v_env_1263_, lean_object* v_as_1264_, lean_object* v_start_1265_, lean_object* v_stop_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0(v_env_1263_, v_as_1264_, v_start_1265_, v_stop_1266_);
lean_dec(v_stop_1266_);
lean_dec(v_start_1265_);
lean_dec_ref(v_as_1264_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3(lean_object* v___f_1268_, lean_object* v_env_1269_, lean_object* v_s_1270_, uint8_t v_level_1271_){
_start:
{
lean_object* v_entries_1272_; uint8_t v___x_1273_; uint8_t v___x_1274_; 
v_entries_1272_ = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries___redArg(v_s_1270_, v___f_1268_);
v___x_1273_ = 2;
v___x_1274_ = l_Lean_instDecidableEqOLeanLevel(v_level_1271_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v_entries_1277_; 
v___x_1275_ = lean_unsigned_to_nat(0u);
v___x_1276_ = lean_array_get_size(v_entries_1272_);
v_entries_1277_ = l_Array_filterMapM___at___00Lean_Compiler_LCNF_mkSigDeclExt_spec__0(v_env_1269_, v_entries_1272_, v___x_1275_, v___x_1276_);
lean_dec_ref(v_entries_1272_);
return v_entries_1277_;
}
else
{
lean_dec_ref(v_env_1269_);
return v_entries_1272_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3___boxed(lean_object* v___f_1278_, lean_object* v_env_1279_, lean_object* v_s_1280_, lean_object* v_level_1281_){
_start:
{
uint8_t v_level_boxed_1282_; lean_object* v_res_1283_; 
v_level_boxed_1282_ = lean_unbox(v_level_1281_);
v_res_1283_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__3(v___f_1278_, v_env_1279_, v_s_1280_, v_level_boxed_1282_);
lean_dec_ref(v_s_1280_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4(lean_object* v___x_1284_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4___boxed(lean_object* v___x_1287_, lean_object* v___y_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4(v___x_1287_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5(lean_object* v___x_1290_, lean_object* v_x_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1290_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5___boxed(lean_object* v___x_1295_, lean_object* v_x_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5(v___x_1295_, v_x_1296_, v___y_1297_);
lean_dec_ref(v___y_1297_);
lean_dec_ref(v_x_1296_);
return v_res_1299_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4(void){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1305_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4, &l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4_once, _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__4);
v___x_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
return v___x_1307_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___f_1309_; 
v___x_1308_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5, &l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5_once, _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5);
v___f_1309_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkSigDeclExt___lam__4___boxed), 2, 1);
lean_closure_set(v___f_1309_, 0, v___x_1308_);
return v___f_1309_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___f_1311_; 
v___x_1310_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5, &l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5_once, _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__5);
v___f_1311_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkSigDeclExt___lam__5___boxed), 4, 1);
lean_closure_set(v___f_1311_, 0, v___x_1310_);
return v___f_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt(uint8_t v_phase_1312_, lean_object* v_name_1313_){
_start:
{
lean_object* v___f_1315_; lean_object* v___f_1316_; lean_object* v___f_1317_; lean_object* v___f_1318_; lean_object* v___f_1319_; uint8_t v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___f_1315_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__0));
v___f_1316_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__1));
v___f_1317_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkSigDeclExt___closed__3));
v___f_1318_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6, &l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6_once, _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__6);
v___f_1319_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7, &l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7_once, _init_l_Lean_Compiler_LCNF_mkSigDeclExt___closed__7);
v___x_1320_ = l_Lean_Compiler_LCNF_Phase_toPurity(v_phase_1312_);
v___x_1321_ = lean_box(v___x_1320_);
v___x_1322_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_statsFn___boxed), 3, 2);
lean_closure_set(v___x_1322_, 0, v___x_1321_);
lean_closure_set(v___x_1322_, 1, lean_box(0));
v___x_1323_ = lean_box(0);
v___x_1324_ = lean_box(v_phase_1312_);
v___x_1325_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn___boxed), 6, 2);
lean_closure_set(v___x_1325_, 0, lean_box(0));
lean_closure_set(v___x_1325_, 1, v___x_1324_);
v___x_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
v___x_1327_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1327_, 0, v_name_1313_);
lean_ctor_set(v___x_1327_, 1, v___f_1318_);
lean_ctor_set(v___x_1327_, 2, v___f_1319_);
lean_ctor_set(v___x_1327_, 3, v___f_1315_);
lean_ctor_set(v___x_1327_, 4, v___f_1317_);
lean_ctor_set(v___x_1327_, 5, v___x_1322_);
lean_ctor_set(v___x_1327_, 6, v___x_1323_);
lean_ctor_set(v___x_1327_, 7, v___x_1326_);
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
lean_ctor_set(v___x_1328_, 1, v___f_1316_);
v___x_1329_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkSigDeclExt___boxed(lean_object* v_phase_1330_, lean_object* v_name_1331_, lean_object* v_a_1332_){
_start:
{
uint8_t v_phase_boxed_1333_; lean_object* v_res_1334_; 
v_phase_boxed_1333_ = lean_unbox(v_phase_1330_);
v_res_1334_ = l_Lean_Compiler_LCNF_mkSigDeclExt(v_phase_boxed_1333_, v_name_1331_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_(){
_start:
{
uint8_t v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1342_ = 2;
v___x_1343_ = ((lean_object*)(l_Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_));
v___x_1344_ = l_Lean_Compiler_LCNF_mkSigDeclExt(v___x_1342_, v___x_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2____boxed(lean_object* v_a_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_();
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(lean_object* v_as_1347_, lean_object* v_k_1348_, lean_object* v_x_1349_, lean_object* v_x_1350_){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v_m_1353_; lean_object* v_a_1354_; uint8_t v___x_1355_; 
v___x_1351_ = lean_nat_add(v_x_1349_, v_x_1350_);
v___x_1352_ = lean_unsigned_to_nat(1u);
v_m_1353_ = lean_nat_shiftr(v___x_1351_, v___x_1352_);
lean_dec(v___x_1351_);
v_a_1354_ = lean_array_fget_borrowed(v_as_1347_, v_m_1353_);
v___x_1355_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__2(v_a_1354_, v_k_1348_);
if (v___x_1355_ == 0)
{
uint8_t v___x_1356_; 
lean_dec(v_x_1350_);
v___x_1356_ = l_Lean_Compiler_LCNF_mkDeclExt___lam__2(v_k_1348_, v_a_1354_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; 
lean_dec(v_m_1353_);
lean_dec(v_x_1349_);
lean_inc(v_a_1354_);
v___x_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1357_, 0, v_a_1354_);
return v___x_1357_;
}
else
{
lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1358_ = lean_unsigned_to_nat(0u);
v___x_1359_ = lean_nat_dec_eq(v_m_1353_, v___x_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; uint8_t v___x_1361_; 
v___x_1360_ = lean_nat_sub(v_m_1353_, v___x_1352_);
lean_dec(v_m_1353_);
v___x_1361_ = lean_nat_dec_lt(v___x_1360_, v_x_1349_);
if (v___x_1361_ == 0)
{
v_x_1350_ = v___x_1360_;
goto _start;
}
else
{
lean_object* v___x_1363_; 
lean_dec(v___x_1360_);
lean_dec(v_x_1349_);
v___x_1363_ = lean_box(0);
return v___x_1363_;
}
}
else
{
lean_object* v___x_1364_; 
lean_dec(v_m_1353_);
lean_dec(v_x_1349_);
v___x_1364_ = lean_box(0);
return v___x_1364_;
}
}
}
else
{
lean_object* v___x_1365_; uint8_t v___x_1366_; 
lean_dec(v_x_1349_);
v___x_1365_ = lean_nat_add(v_m_1353_, v___x_1352_);
lean_dec(v_m_1353_);
v___x_1366_ = lean_nat_dec_le(v___x_1365_, v_x_1350_);
if (v___x_1366_ == 0)
{
lean_object* v___x_1367_; 
lean_dec(v___x_1365_);
lean_dec(v_x_1350_);
v___x_1367_ = lean_box(0);
return v___x_1367_;
}
else
{
v_x_1349_ = v___x_1365_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg___boxed(lean_object* v_as_1369_, lean_object* v_k_1370_, lean_object* v_x_1371_, lean_object* v_x_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(v_as_1369_, v_k_1370_, v_x_1371_, v_x_1372_);
lean_dec_ref(v_k_1370_);
lean_dec_ref(v_as_1369_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1374_, lean_object* v_vals_1375_, lean_object* v_i_1376_, lean_object* v_k_1377_){
_start:
{
lean_object* v___x_1378_; uint8_t v___x_1379_; 
v___x_1378_ = lean_array_get_size(v_keys_1374_);
v___x_1379_ = lean_nat_dec_lt(v_i_1376_, v___x_1378_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; 
lean_dec(v_i_1376_);
v___x_1380_ = lean_box(0);
return v___x_1380_;
}
else
{
lean_object* v_k_x27_1381_; uint8_t v___x_1382_; 
v_k_x27_1381_ = lean_array_fget_borrowed(v_keys_1374_, v_i_1376_);
v___x_1382_ = lean_name_eq(v_k_1377_, v_k_x27_1381_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = lean_unsigned_to_nat(1u);
v___x_1384_ = lean_nat_add(v_i_1376_, v___x_1383_);
lean_dec(v_i_1376_);
v_i_1376_ = v___x_1384_;
goto _start;
}
else
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = lean_array_fget_borrowed(v_vals_1375_, v_i_1376_);
lean_dec(v_i_1376_);
lean_inc(v___x_1386_);
v___x_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
return v___x_1387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1388_, lean_object* v_vals_1389_, lean_object* v_i_1390_, lean_object* v_k_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1388_, v_vals_1389_, v_i_1390_, v_k_1391_);
lean_dec(v_k_1391_);
lean_dec_ref(v_vals_1389_);
lean_dec_ref(v_keys_1388_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(lean_object* v_x_1393_, size_t v_x_1394_, lean_object* v_x_1395_){
_start:
{
if (lean_obj_tag(v_x_1393_) == 0)
{
lean_object* v_es_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1417_; 
v_es_1396_ = lean_ctor_get(v_x_1393_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_x_1393_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1398_ = v_x_1393_;
v_isShared_1399_ = v_isSharedCheck_1417_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_es_1396_);
lean_dec(v_x_1393_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1417_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; size_t v___x_1401_; size_t v___x_1402_; size_t v___x_1403_; lean_object* v_j_1404_; lean_object* v___x_1405_; 
v___x_1400_ = lean_box(2);
v___x_1401_ = ((size_t)5ULL);
v___x_1402_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0_spec__0___redArg___closed__1);
v___x_1403_ = lean_usize_land(v_x_1394_, v___x_1402_);
v_j_1404_ = lean_usize_to_nat(v___x_1403_);
v___x_1405_ = lean_array_get(v___x_1400_, v_es_1396_, v_j_1404_);
lean_dec(v_j_1404_);
lean_dec_ref(v_es_1396_);
switch(lean_obj_tag(v___x_1405_))
{
case 0:
{
lean_object* v_key_1406_; lean_object* v_val_1407_; uint8_t v___x_1408_; 
v_key_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_key_1406_);
v_val_1407_ = lean_ctor_get(v___x_1405_, 1);
lean_inc(v_val_1407_);
lean_dec_ref(v___x_1405_);
v___x_1408_ = lean_name_eq(v_x_1395_, v_key_1406_);
lean_dec(v_key_1406_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; 
lean_dec(v_val_1407_);
lean_del_object(v___x_1398_);
v___x_1409_ = lean_box(0);
return v___x_1409_;
}
else
{
lean_object* v___x_1411_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set_tag(v___x_1398_, 1);
lean_ctor_set(v___x_1398_, 0, v_val_1407_);
v___x_1411_ = v___x_1398_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_val_1407_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
case 1:
{
lean_object* v_node_1413_; size_t v___x_1414_; 
lean_del_object(v___x_1398_);
v_node_1413_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_node_1413_);
lean_dec_ref(v___x_1405_);
v___x_1414_ = lean_usize_shift_right(v_x_1394_, v___x_1401_);
v_x_1393_ = v_node_1413_;
v_x_1394_ = v___x_1414_;
goto _start;
}
default: 
{
lean_object* v___x_1416_; 
lean_del_object(v___x_1398_);
v___x_1416_ = lean_box(0);
return v___x_1416_;
}
}
}
}
else
{
lean_object* v_ks_1418_; lean_object* v_vs_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v_ks_1418_ = lean_ctor_get(v_x_1393_, 0);
lean_inc_ref(v_ks_1418_);
v_vs_1419_ = lean_ctor_get(v_x_1393_, 1);
lean_inc_ref(v_vs_1419_);
lean_dec_ref(v_x_1393_);
v___x_1420_ = lean_unsigned_to_nat(0u);
v___x_1421_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1418_, v_vs_1419_, v___x_1420_, v_x_1395_);
lean_dec_ref(v_vs_1419_);
lean_dec_ref(v_ks_1418_);
return v___x_1421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_1422_, lean_object* v_x_1423_, lean_object* v_x_1424_){
_start:
{
size_t v_x_429__boxed_1425_; lean_object* v_res_1426_; 
v_x_429__boxed_1425_ = lean_unbox_usize(v_x_1423_);
lean_dec(v_x_1423_);
v_res_1426_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(v_x_1422_, v_x_429__boxed_1425_, v_x_1424_);
lean_dec(v_x_1424_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(lean_object* v_x_1427_, lean_object* v_x_1428_){
_start:
{
uint64_t v___y_1430_; 
if (lean_obj_tag(v_x_1428_) == 0)
{
uint64_t v___x_1433_; 
v___x_1433_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
v___y_1430_ = v___x_1433_;
goto v___jp_1429_;
}
else
{
uint64_t v_hash_1434_; 
v_hash_1434_ = lean_ctor_get_uint64(v_x_1428_, sizeof(void*)*2);
v___y_1430_ = v_hash_1434_;
goto v___jp_1429_;
}
v___jp_1429_:
{
size_t v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = lean_uint64_to_usize(v___y_1430_);
v___x_1432_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(v_x_1427_, v___x_1431_, v_x_1428_);
return v___x_1432_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg___boxed(lean_object* v_x_1435_, lean_object* v_x_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v_x_1435_, v_x_1436_);
lean_dec(v_x_1436_);
return v_res_1437_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2(void){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1440_ = ((lean_object*)(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__1));
v___x_1441_ = ((lean_object*)(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__0));
v___x_1442_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_1441_, v___x_1440_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f(uint8_t v_pu_1443_, lean_object* v_env_1444_, lean_object* v_ext_1445_, lean_object* v_declName_1446_){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1454_; 
v___x_1447_ = lean_obj_once(&l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2, &l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2_once, _init_l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2);
v___x_1454_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1444_, v_declName_1446_);
if (lean_obj_tag(v___x_1454_) == 0)
{
goto v___jp_1448_;
}
else
{
lean_object* v_val_1455_; lean_object* v_tmpDecl_1490_; lean_object* v_toSignature_1491_; lean_object* v_value_1492_; uint8_t v_recursive_1493_; lean_object* v_inlineAttr_x3f_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1521_; 
v_val_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_val_1455_);
lean_dec_ref(v___x_1454_);
v_tmpDecl_1490_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v_pu_1443_);
v_toSignature_1491_ = lean_ctor_get(v_tmpDecl_1490_, 0);
v_value_1492_ = lean_ctor_get(v_tmpDecl_1490_, 1);
v_recursive_1493_ = lean_ctor_get_uint8(v_tmpDecl_1490_, sizeof(void*)*3);
v_inlineAttr_x3f_1494_ = lean_ctor_get(v_tmpDecl_1490_, 2);
v_isSharedCheck_1521_ = !lean_is_exclusive(v_tmpDecl_1490_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1496_ = v_tmpDecl_1490_;
v_isShared_1497_ = v_isSharedCheck_1521_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_inlineAttr_x3f_1494_);
lean_inc(v_value_1492_);
lean_inc(v_toSignature_1491_);
lean_dec(v_tmpDecl_1490_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1521_;
goto v_resetjp_1495_;
}
v___jp_1456_:
{
lean_object* v_tmpDecl_1457_; lean_object* v_toSignature_1458_; lean_object* v_value_1459_; uint8_t v_recursive_1460_; lean_object* v_inlineAttr_x3f_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1489_; 
v_tmpDecl_1457_ = l_Lean_Compiler_LCNF_instInhabitedDecl_default(v_pu_1443_);
v_toSignature_1458_ = lean_ctor_get(v_tmpDecl_1457_, 0);
v_value_1459_ = lean_ctor_get(v_tmpDecl_1457_, 1);
v_recursive_1460_ = lean_ctor_get_uint8(v_tmpDecl_1457_, sizeof(void*)*3);
v_inlineAttr_x3f_1461_ = lean_ctor_get(v_tmpDecl_1457_, 2);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_tmpDecl_1457_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1463_ = v_tmpDecl_1457_;
v_isShared_1464_ = v_isSharedCheck_1489_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_inlineAttr_x3f_1461_);
lean_inc(v_value_1459_);
lean_inc(v_toSignature_1458_);
lean_dec(v_tmpDecl_1457_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1489_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v_levelParams_1465_; lean_object* v_type_1466_; lean_object* v_params_1467_; uint8_t v_safe_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1487_; 
v_levelParams_1465_ = lean_ctor_get(v_toSignature_1458_, 1);
v_type_1466_ = lean_ctor_get(v_toSignature_1458_, 2);
v_params_1467_ = lean_ctor_get(v_toSignature_1458_, 3);
v_safe_1468_ = lean_ctor_get_uint8(v_toSignature_1458_, sizeof(void*)*4);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_toSignature_1458_);
if (v_isSharedCheck_1487_ == 0)
{
lean_object* v_unused_1488_; 
v_unused_1488_ = lean_ctor_get(v_toSignature_1458_, 0);
lean_dec(v_unused_1488_);
v___x_1470_ = v_toSignature_1458_;
v_isShared_1471_ = v_isSharedCheck_1487_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_params_1467_);
lean_inc(v_type_1466_);
lean_inc(v_levelParams_1465_);
lean_dec(v_toSignature_1458_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1487_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
uint8_t v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; 
v___x_1472_ = 0;
v___x_1473_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1447_, v_ext_1445_, v_env_1444_, v_val_1455_, v___x_1472_);
lean_dec(v_val_1455_);
v___x_1474_ = lean_unsigned_to_nat(0u);
v___x_1475_ = lean_array_get_size(v___x_1473_);
v___x_1476_ = lean_nat_dec_lt(v___x_1474_, v___x_1475_);
if (v___x_1476_ == 0)
{
lean_dec_ref(v___x_1473_);
lean_del_object(v___x_1470_);
lean_dec_ref(v_params_1467_);
lean_dec_ref(v_type_1466_);
lean_dec(v_levelParams_1465_);
lean_del_object(v___x_1463_);
lean_dec(v_inlineAttr_x3f_1461_);
lean_dec_ref(v_value_1459_);
goto v___jp_1448_;
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___x_1477_ = lean_unsigned_to_nat(1u);
v___x_1478_ = lean_nat_sub(v___x_1475_, v___x_1477_);
v___x_1479_ = lean_nat_dec_le(v___x_1474_, v___x_1478_);
if (v___x_1479_ == 0)
{
lean_dec(v___x_1478_);
lean_dec_ref(v___x_1473_);
lean_del_object(v___x_1470_);
lean_dec_ref(v_params_1467_);
lean_dec_ref(v_type_1466_);
lean_dec(v_levelParams_1465_);
lean_del_object(v___x_1463_);
lean_dec(v_inlineAttr_x3f_1461_);
lean_dec_ref(v_value_1459_);
goto v___jp_1448_;
}
else
{
lean_object* v___x_1481_; 
lean_inc(v_declName_1446_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v_declName_1446_);
v___x_1481_ = v___x_1470_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_declName_1446_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_levelParams_1465_);
lean_ctor_set(v_reuseFailAlloc_1486_, 2, v_type_1466_);
lean_ctor_set(v_reuseFailAlloc_1486_, 3, v_params_1467_);
lean_ctor_set_uint8(v_reuseFailAlloc_1486_, sizeof(void*)*4, v_safe_1468_);
v___x_1481_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v_tmpDecl_1483_; 
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 0, v___x_1481_);
v_tmpDecl_1483_ = v___x_1463_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_value_1459_);
lean_ctor_set(v_reuseFailAlloc_1485_, 2, v_inlineAttr_x3f_1461_);
lean_ctor_set_uint8(v_reuseFailAlloc_1485_, sizeof(void*)*3, v_recursive_1460_);
v_tmpDecl_1483_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(v___x_1473_, v_tmpDecl_1483_, v___x_1474_, v___x_1478_);
lean_dec_ref(v_tmpDecl_1483_);
lean_dec_ref(v___x_1473_);
if (lean_obj_tag(v___x_1484_) == 0)
{
goto v___jp_1448_;
}
else
{
lean_dec(v_declName_1446_);
lean_dec_ref(v_env_1444_);
return v___x_1484_;
}
}
}
}
}
}
}
}
v_resetjp_1495_:
{
lean_object* v_levelParams_1498_; lean_object* v_type_1499_; lean_object* v_params_1500_; uint8_t v_safe_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1519_; 
v_levelParams_1498_ = lean_ctor_get(v_toSignature_1491_, 1);
v_type_1499_ = lean_ctor_get(v_toSignature_1491_, 2);
v_params_1500_ = lean_ctor_get(v_toSignature_1491_, 3);
v_safe_1501_ = lean_ctor_get_uint8(v_toSignature_1491_, sizeof(void*)*4);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_toSignature_1491_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; 
v_unused_1520_ = lean_ctor_get(v_toSignature_1491_, 0);
lean_dec(v_unused_1520_);
v___x_1503_ = v_toSignature_1491_;
v_isShared_1504_ = v_isSharedCheck_1519_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_params_1500_);
lean_inc(v_type_1499_);
lean_inc(v_levelParams_1498_);
lean_dec(v_toSignature_1491_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1519_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; uint8_t v___x_1508_; 
v___x_1505_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1447_, v_ext_1445_, v_env_1444_, v_val_1455_);
v___x_1506_ = lean_unsigned_to_nat(0u);
v___x_1507_ = lean_array_get_size(v___x_1505_);
v___x_1508_ = lean_nat_dec_lt(v___x_1506_, v___x_1507_);
if (v___x_1508_ == 0)
{
lean_dec_ref(v___x_1505_);
lean_del_object(v___x_1503_);
lean_dec_ref(v_params_1500_);
lean_dec_ref(v_type_1499_);
lean_dec(v_levelParams_1498_);
lean_del_object(v___x_1496_);
lean_dec(v_inlineAttr_x3f_1494_);
lean_dec_ref(v_value_1492_);
goto v___jp_1456_;
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; 
v___x_1509_ = lean_unsigned_to_nat(1u);
v___x_1510_ = lean_nat_sub(v___x_1507_, v___x_1509_);
v___x_1511_ = lean_nat_dec_le(v___x_1506_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_dec(v___x_1510_);
lean_dec_ref(v___x_1505_);
lean_del_object(v___x_1503_);
lean_dec_ref(v_params_1500_);
lean_dec_ref(v_type_1499_);
lean_dec(v_levelParams_1498_);
lean_del_object(v___x_1496_);
lean_dec(v_inlineAttr_x3f_1494_);
lean_dec_ref(v_value_1492_);
goto v___jp_1456_;
}
else
{
lean_object* v___x_1513_; 
lean_inc(v_declName_1446_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 0, v_declName_1446_);
v___x_1513_ = v___x_1503_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_declName_1446_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_levelParams_1498_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_type_1499_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v_params_1500_);
lean_ctor_set_uint8(v_reuseFailAlloc_1518_, sizeof(void*)*4, v_safe_1501_);
v___x_1513_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v_tmpDecl_1515_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1513_);
v_tmpDecl_1515_ = v___x_1496_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_value_1492_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_inlineAttr_x3f_1494_);
lean_ctor_set_uint8(v_reuseFailAlloc_1517_, sizeof(void*)*3, v_recursive_1493_);
v_tmpDecl_1515_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(v___x_1505_, v_tmpDecl_1515_, v___x_1506_, v___x_1510_);
lean_dec_ref(v_tmpDecl_1515_);
lean_dec_ref(v___x_1505_);
if (lean_obj_tag(v___x_1516_) == 0)
{
goto v___jp_1456_;
}
else
{
lean_dec(v_val_1455_);
lean_dec(v_declName_1446_);
lean_dec_ref(v_env_1444_);
return v___x_1516_;
}
}
}
}
}
}
}
}
v___jp_1448_:
{
lean_object* v_toEnvExtension_1449_; lean_object* v_asyncMode_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v_toEnvExtension_1449_ = lean_ctor_get(v_ext_1445_, 0);
v_asyncMode_1450_ = lean_ctor_get(v_toEnvExtension_1449_, 2);
v___x_1451_ = lean_box(0);
v___x_1452_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1447_, v_ext_1445_, v_env_1444_, v_asyncMode_1450_, v___x_1451_);
v___x_1453_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_1452_, v_declName_1446_);
lean_dec(v_declName_1446_);
return v___x_1453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclCore_x3f___boxed(lean_object* v_pu_1522_, lean_object* v_env_1523_, lean_object* v_ext_1524_, lean_object* v_declName_1525_){
_start:
{
uint8_t v_pu_boxed_1526_; lean_object* v_res_1527_; 
v_pu_boxed_1526_ = lean_unbox(v_pu_1522_);
v_res_1527_ = l_Lean_Compiler_LCNF_getDeclCore_x3f(v_pu_boxed_1526_, v_env_1523_, v_ext_1524_, v_declName_1525_);
lean_dec_ref(v_ext_1524_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0(lean_object* v_00_u03b2_1528_, lean_object* v_x_1529_, lean_object* v_x_1530_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v_x_1529_, v_x_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___boxed(lean_object* v_00_u03b2_1532_, lean_object* v_x_1533_, lean_object* v_x_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0(v_00_u03b2_1532_, v_x_1533_, v_x_1534_);
lean_dec(v_x_1534_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1(lean_object* v_as_1536_, lean_object* v_k_1537_, lean_object* v_x_1538_, lean_object* v_x_1539_, lean_object* v_x_1540_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___redArg(v_as_1536_, v_k_1537_, v_x_1538_, v_x_1539_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1___boxed(lean_object* v_as_1542_, lean_object* v_k_1543_, lean_object* v_x_1544_, lean_object* v_x_1545_, lean_object* v_x_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__1(v_as_1542_, v_k_1543_, v_x_1544_, v_x_1545_, v_x_1546_);
lean_dec_ref(v_k_1543_);
lean_dec_ref(v_as_1542_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1548_, lean_object* v_x_1549_, size_t v_x_1550_, lean_object* v_x_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___redArg(v_x_1549_, v_x_1550_, v_x_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1553_, lean_object* v_x_1554_, lean_object* v_x_1555_, lean_object* v_x_1556_){
_start:
{
size_t v_x_651__boxed_1557_; lean_object* v_res_1558_; 
v_x_651__boxed_1557_ = lean_unbox_usize(v_x_1555_);
lean_dec(v_x_1555_);
v_res_1558_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0(v_00_u03b2_1553_, v_x_1554_, v_x_651__boxed_1557_, v_x_1556_);
lean_dec(v_x_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1559_, lean_object* v_keys_1560_, lean_object* v_vals_1561_, lean_object* v_heq_1562_, lean_object* v_i_1563_, lean_object* v_k_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1560_, v_vals_1561_, v_i_1563_, v_k_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1566_, lean_object* v_keys_1567_, lean_object* v_vals_1568_, lean_object* v_heq_1569_, lean_object* v_i_1570_, lean_object* v_k_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1566_, v_keys_1567_, v_vals_1568_, v_heq_1569_, v_i_1570_, v_k_1571_);
lean_dec(v_k_1571_);
lean_dec_ref(v_vals_1568_);
lean_dec_ref(v_keys_1567_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(lean_object* v_as_1573_, lean_object* v_k_1574_, lean_object* v_x_1575_, lean_object* v_x_1576_){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v_m_1579_; lean_object* v_a_1580_; uint8_t v___x_1581_; 
v___x_1577_ = lean_nat_add(v_x_1575_, v_x_1576_);
v___x_1578_ = lean_unsigned_to_nat(1u);
v_m_1579_ = lean_nat_shiftr(v___x_1577_, v___x_1578_);
lean_dec(v___x_1577_);
v_a_1580_ = lean_array_fget_borrowed(v_as_1573_, v_m_1579_);
v___x_1581_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(v_a_1580_, v_k_1574_);
if (v___x_1581_ == 0)
{
uint8_t v___x_1582_; 
lean_dec(v_x_1576_);
v___x_1582_ = l_Lean_Compiler_LCNF_mkSigDeclExt___lam__2(v_k_1574_, v_a_1580_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; 
lean_dec(v_m_1579_);
lean_dec(v_x_1575_);
lean_inc(v_a_1580_);
v___x_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1583_, 0, v_a_1580_);
return v___x_1583_;
}
else
{
lean_object* v___x_1584_; uint8_t v___x_1585_; 
v___x_1584_ = lean_unsigned_to_nat(0u);
v___x_1585_ = lean_nat_dec_eq(v_m_1579_, v___x_1584_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; uint8_t v___x_1587_; 
v___x_1586_ = lean_nat_sub(v_m_1579_, v___x_1578_);
lean_dec(v_m_1579_);
v___x_1587_ = lean_nat_dec_lt(v___x_1586_, v_x_1575_);
if (v___x_1587_ == 0)
{
v_x_1576_ = v___x_1586_;
goto _start;
}
else
{
lean_object* v___x_1589_; 
lean_dec(v___x_1586_);
lean_dec(v_x_1575_);
v___x_1589_ = lean_box(0);
return v___x_1589_;
}
}
else
{
lean_object* v___x_1590_; 
lean_dec(v_m_1579_);
lean_dec(v_x_1575_);
v___x_1590_ = lean_box(0);
return v___x_1590_;
}
}
}
else
{
lean_object* v___x_1591_; uint8_t v___x_1592_; 
lean_dec(v_x_1575_);
v___x_1591_ = lean_nat_add(v_m_1579_, v___x_1578_);
lean_dec(v_m_1579_);
v___x_1592_ = lean_nat_dec_le(v___x_1591_, v_x_1576_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; 
lean_dec(v___x_1591_);
lean_dec(v_x_1576_);
v___x_1593_ = lean_box(0);
return v___x_1593_;
}
else
{
v_x_1575_ = v___x_1591_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg___boxed(lean_object* v_as_1595_, lean_object* v_k_1596_, lean_object* v_x_1597_, lean_object* v_x_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(v_as_1595_, v_k_1596_, v_x_1597_, v_x_1598_);
lean_dec_ref(v_k_1596_);
lean_dec_ref(v_as_1595_);
return v_res_1599_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getSigCore_x3f___closed__0(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1600_ = ((lean_object*)(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__1));
v___x_1601_ = ((lean_object*)(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__0));
v___x_1602_ = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_1601_, v___x_1600_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSigCore_x3f(uint8_t v_pu_1603_, lean_object* v_env_1604_, lean_object* v_ext_1605_, lean_object* v_declName_1606_){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1614_; 
v___x_1607_ = lean_obj_once(&l_Lean_Compiler_LCNF_getSigCore_x3f___closed__0, &l_Lean_Compiler_LCNF_getSigCore_x3f___closed__0_once, _init_l_Lean_Compiler_LCNF_getSigCore_x3f___closed__0);
v___x_1614_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1604_, v_declName_1606_);
if (lean_obj_tag(v___x_1614_) == 0)
{
goto v___jp_1608_;
}
else
{
lean_object* v_val_1615_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; 
v_val_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_val_1615_);
lean_dec_ref(v___x_1614_);
v___x_1639_ = l___private_Lean_Environment_0__Lean_PersistentEnvExtension_getModuleIREntries_unsafe__1(lean_box(0), lean_box(0), lean_box(0), v___x_1607_, v_ext_1605_, v_env_1604_, v_val_1615_);
v___x_1640_ = lean_unsigned_to_nat(0u);
v___x_1641_ = lean_array_get_size(v___x_1639_);
v___x_1642_ = lean_nat_dec_lt(v___x_1640_, v___x_1641_);
if (v___x_1642_ == 0)
{
lean_dec_ref(v___x_1639_);
goto v___jp_1616_;
}
else
{
lean_object* v_tmpSig_1643_; lean_object* v_levelParams_1644_; lean_object* v_type_1645_; lean_object* v_params_1646_; uint8_t v_safe_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1658_; 
v_tmpSig_1643_ = l_Lean_Compiler_LCNF_instInhabitedSignature_default(v_pu_1603_);
v_levelParams_1644_ = lean_ctor_get(v_tmpSig_1643_, 1);
v_type_1645_ = lean_ctor_get(v_tmpSig_1643_, 2);
v_params_1646_ = lean_ctor_get(v_tmpSig_1643_, 3);
v_safe_1647_ = lean_ctor_get_uint8(v_tmpSig_1643_, sizeof(void*)*4);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_tmpSig_1643_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; 
v_unused_1659_ = lean_ctor_get(v_tmpSig_1643_, 0);
lean_dec(v_unused_1659_);
v___x_1649_ = v_tmpSig_1643_;
v_isShared_1650_ = v_isSharedCheck_1658_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_params_1646_);
lean_inc(v_type_1645_);
lean_inc(v_levelParams_1644_);
lean_dec(v_tmpSig_1643_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1658_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1651_ = lean_unsigned_to_nat(1u);
v___x_1652_ = lean_nat_sub(v___x_1641_, v___x_1651_);
v___x_1653_ = lean_nat_dec_le(v___x_1640_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_dec(v___x_1652_);
lean_del_object(v___x_1649_);
lean_dec_ref(v_params_1646_);
lean_dec_ref(v_type_1645_);
lean_dec(v_levelParams_1644_);
lean_dec_ref(v___x_1639_);
goto v___jp_1616_;
}
else
{
lean_object* v_tmpSig_1655_; 
lean_inc(v_declName_1606_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v_declName_1606_);
v_tmpSig_1655_ = v___x_1649_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_declName_1606_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_levelParams_1644_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v_type_1645_);
lean_ctor_set(v_reuseFailAlloc_1657_, 3, v_params_1646_);
lean_ctor_set_uint8(v_reuseFailAlloc_1657_, sizeof(void*)*4, v_safe_1647_);
v_tmpSig_1655_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(v___x_1639_, v_tmpSig_1655_, v___x_1640_, v___x_1652_);
lean_dec_ref(v_tmpSig_1655_);
lean_dec_ref(v___x_1639_);
if (lean_obj_tag(v___x_1656_) == 0)
{
goto v___jp_1616_;
}
else
{
lean_dec(v_val_1615_);
lean_dec(v_declName_1606_);
lean_dec_ref(v_env_1604_);
return v___x_1656_;
}
}
}
}
}
v___jp_1616_:
{
uint8_t v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1617_ = 0;
v___x_1618_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1607_, v_ext_1605_, v_env_1604_, v_val_1615_, v___x_1617_);
lean_dec(v_val_1615_);
v___x_1619_ = lean_unsigned_to_nat(0u);
v___x_1620_ = lean_array_get_size(v___x_1618_);
v___x_1621_ = lean_nat_dec_lt(v___x_1619_, v___x_1620_);
if (v___x_1621_ == 0)
{
lean_dec_ref(v___x_1618_);
goto v___jp_1608_;
}
else
{
lean_object* v_tmpSig_1622_; lean_object* v_levelParams_1623_; lean_object* v_type_1624_; lean_object* v_params_1625_; uint8_t v_safe_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1637_; 
v_tmpSig_1622_ = l_Lean_Compiler_LCNF_instInhabitedSignature_default(v_pu_1603_);
v_levelParams_1623_ = lean_ctor_get(v_tmpSig_1622_, 1);
v_type_1624_ = lean_ctor_get(v_tmpSig_1622_, 2);
v_params_1625_ = lean_ctor_get(v_tmpSig_1622_, 3);
v_safe_1626_ = lean_ctor_get_uint8(v_tmpSig_1622_, sizeof(void*)*4);
v_isSharedCheck_1637_ = !lean_is_exclusive(v_tmpSig_1622_);
if (v_isSharedCheck_1637_ == 0)
{
lean_object* v_unused_1638_; 
v_unused_1638_ = lean_ctor_get(v_tmpSig_1622_, 0);
lean_dec(v_unused_1638_);
v___x_1628_ = v_tmpSig_1622_;
v_isShared_1629_ = v_isSharedCheck_1637_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_params_1625_);
lean_inc(v_type_1624_);
lean_inc(v_levelParams_1623_);
lean_dec(v_tmpSig_1622_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1637_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1630_ = lean_unsigned_to_nat(1u);
v___x_1631_ = lean_nat_sub(v___x_1620_, v___x_1630_);
v___x_1632_ = lean_nat_dec_le(v___x_1619_, v___x_1631_);
if (v___x_1632_ == 0)
{
lean_dec(v___x_1631_);
lean_del_object(v___x_1628_);
lean_dec_ref(v_params_1625_);
lean_dec_ref(v_type_1624_);
lean_dec(v_levelParams_1623_);
lean_dec_ref(v___x_1618_);
goto v___jp_1608_;
}
else
{
lean_object* v_tmpSig_1634_; 
lean_inc(v_declName_1606_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v_declName_1606_);
v_tmpSig_1634_ = v___x_1628_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_declName_1606_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_levelParams_1623_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v_type_1624_);
lean_ctor_set(v_reuseFailAlloc_1636_, 3, v_params_1625_);
lean_ctor_set_uint8(v_reuseFailAlloc_1636_, sizeof(void*)*4, v_safe_1626_);
v_tmpSig_1634_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(v___x_1618_, v_tmpSig_1634_, v___x_1619_, v___x_1631_);
lean_dec_ref(v_tmpSig_1634_);
lean_dec_ref(v___x_1618_);
if (lean_obj_tag(v___x_1635_) == 0)
{
goto v___jp_1608_;
}
else
{
lean_dec(v_declName_1606_);
lean_dec_ref(v_env_1604_);
return v___x_1635_;
}
}
}
}
}
}
}
v___jp_1608_:
{
lean_object* v_toEnvExtension_1609_; lean_object* v_asyncMode_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v_toEnvExtension_1609_ = lean_ctor_get(v_ext_1605_, 0);
v_asyncMode_1610_ = lean_ctor_get(v_toEnvExtension_1609_, 2);
v___x_1611_ = lean_box(0);
v___x_1612_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1607_, v_ext_1605_, v_env_1604_, v_asyncMode_1610_, v___x_1611_);
v___x_1613_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_1612_, v_declName_1606_);
lean_dec(v_declName_1606_);
return v___x_1613_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSigCore_x3f___boxed(lean_object* v_pu_1660_, lean_object* v_env_1661_, lean_object* v_ext_1662_, lean_object* v_declName_1663_){
_start:
{
uint8_t v_pu_boxed_1664_; lean_object* v_res_1665_; 
v_pu_boxed_1664_ = lean_unbox(v_pu_1660_);
v_res_1665_ = l_Lean_Compiler_LCNF_getSigCore_x3f(v_pu_boxed_1664_, v_env_1661_, v_ext_1662_, v_declName_1663_);
lean_dec_ref(v_ext_1662_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0(lean_object* v_as_1666_, lean_object* v_k_1667_, lean_object* v_x_1668_, lean_object* v_x_1669_, lean_object* v_x_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___redArg(v_as_1666_, v_k_1667_, v_x_1668_, v_x_1669_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0___boxed(lean_object* v_as_1672_, lean_object* v_k_1673_, lean_object* v_x_1674_, lean_object* v_x_1675_, lean_object* v_x_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Array_binSearchAux___at___00Lean_Compiler_LCNF_getSigCore_x3f_spec__0(v_as_1672_, v_k_1673_, v_x_1674_, v_x_1675_, v_x_1676_);
lean_dec_ref(v_k_1673_);
lean_dec_ref(v_as_1672_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(lean_object* v_declName_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v___x_1681_; lean_object* v_env_1682_; uint8_t v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1681_ = lean_st_ref_get(v_a_1679_);
v_env_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc_ref(v_env_1682_);
lean_dec(v___x_1681_);
v___x_1683_ = 0;
v___x_1684_ = l_Lean_Compiler_LCNF_baseExt;
v___x_1685_ = l_Lean_Compiler_LCNF_getDeclCore_x3f(v___x_1683_, v_env_1682_, v___x_1684_, v_declName_1678_);
v___x_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg___boxed(lean_object* v_declName_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(v_declName_1687_, v_a_1688_);
lean_dec(v_a_1688_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f(lean_object* v_declName_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(v_declName_1691_, v_a_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getBaseDecl_x3f___boxed(lean_object* v_declName_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lean_Compiler_LCNF_getBaseDecl_x3f(v_declName_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object* v_declName_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v___x_1704_; lean_object* v_env_1705_; uint8_t v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1704_ = lean_st_ref_get(v_a_1702_);
v_env_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc_ref(v_env_1705_);
lean_dec(v___x_1704_);
v___x_1706_ = 0;
v___x_1707_ = l_Lean_Compiler_LCNF_monoExt;
v___x_1708_ = l_Lean_Compiler_LCNF_getDeclCore_x3f(v___x_1706_, v_env_1705_, v___x_1707_, v_declName_1701_);
v___x_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg___boxed(lean_object* v_declName_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_1710_, v_a_1711_);
lean_dec(v_a_1711_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f(lean_object* v_declName_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_1714_, v_a_1716_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___boxed(lean_object* v_declName_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f(v_declName_1719_, v_a_1720_, v_a_1721_);
lean_dec(v_a_1721_);
lean_dec_ref(v_a_1720_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(lean_object* v_declName_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v___x_1727_; lean_object* v_env_1728_; lean_object* v___x_1729_; lean_object* v_asyncMode_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1727_ = lean_st_ref_get(v_a_1725_);
v_env_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc_ref(v_env_1728_);
lean_dec(v___x_1727_);
v___x_1729_ = l_Lean_Compiler_LCNF_impureExt;
v_asyncMode_1730_ = lean_ctor_get(v___x_1729_, 2);
lean_inc(v_asyncMode_1730_);
v___x_1731_ = lean_obj_once(&l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2, &l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2_once, _init_l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2);
v___x_1732_ = lean_box(0);
v___x_1733_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1731_, v___x_1729_, v_env_1728_, v_asyncMode_1730_, v___x_1732_);
lean_dec(v_asyncMode_1730_);
v___x_1734_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_1733_, v_declName_1724_);
v___x_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg___boxed(lean_object* v_declName_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(v_declName_1736_, v_a_1737_);
lean_dec(v_a_1737_);
lean_dec(v_declName_1736_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f(lean_object* v_declName_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___redArg(v_declName_1740_, v_a_1742_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f___boxed(lean_object* v_declName_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_Compiler_LCNF_getLocalImpureDecl_x3f(v_declName_1745_, v_a_1746_, v_a_1747_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_declName_1745_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1(size_t v_sz_1750_, size_t v_i_1751_, lean_object* v_bs_1752_){
_start:
{
uint8_t v___x_1753_; 
v___x_1753_ = lean_usize_dec_lt(v_i_1751_, v_sz_1750_);
if (v___x_1753_ == 0)
{
return v_bs_1752_;
}
else
{
lean_object* v_v_1754_; lean_object* v_fst_1755_; lean_object* v___x_1756_; lean_object* v_bs_x27_1757_; size_t v___x_1758_; size_t v___x_1759_; lean_object* v___x_1760_; 
v_v_1754_ = lean_array_uget_borrowed(v_bs_1752_, v_i_1751_);
v_fst_1755_ = lean_ctor_get(v_v_1754_, 0);
lean_inc(v_fst_1755_);
v___x_1756_ = lean_unsigned_to_nat(0u);
v_bs_x27_1757_ = lean_array_uset(v_bs_1752_, v_i_1751_, v___x_1756_);
v___x_1758_ = ((size_t)1ULL);
v___x_1759_ = lean_usize_add(v_i_1751_, v___x_1758_);
v___x_1760_ = lean_array_uset(v_bs_x27_1757_, v_i_1751_, v_fst_1755_);
v_i_1751_ = v___x_1759_;
v_bs_1752_ = v___x_1760_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1___boxed(lean_object* v_sz_1762_, lean_object* v_i_1763_, lean_object* v_bs_1764_){
_start:
{
size_t v_sz_boxed_1765_; size_t v_i_boxed_1766_; lean_object* v_res_1767_; 
v_sz_boxed_1765_ = lean_unbox_usize(v_sz_1762_);
lean_dec(v_sz_1762_);
v_i_boxed_1766_ = lean_unbox_usize(v_i_1763_);
lean_dec(v_i_1763_);
v_res_1767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1(v_sz_boxed_1765_, v_i_boxed_1766_, v_bs_1764_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___lam__0(lean_object* v_ps_1768_, lean_object* v_k_1769_, lean_object* v_v_1770_){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1771_, 0, v_k_1769_);
lean_ctor_set(v___x_1771_, 1, v_v_1770_);
v___x_1772_ = lean_array_push(v_ps_1768_, v___x_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(lean_object* v_m_1776_){
_start:
{
lean_object* v___f_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___f_1777_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__0));
v___x_1778_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___closed__1));
v___x_1779_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_sortedEntries_spec__0___redArg(v_m_1776_, v___f_1777_, v___x_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg___boxed(lean_object* v_m_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(v_m_1780_);
lean_dec_ref(v_m_1780_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg(lean_object* v_a_1782_){
_start:
{
lean_object* v___x_1784_; lean_object* v_env_1785_; lean_object* v___x_1786_; lean_object* v_asyncMode_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; size_t v_sz_1792_; size_t v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1784_ = lean_st_ref_get(v_a_1782_);
v_env_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc_ref(v_env_1785_);
lean_dec(v___x_1784_);
v___x_1786_ = l_Lean_Compiler_LCNF_impureExt;
v_asyncMode_1787_ = lean_ctor_get(v___x_1786_, 2);
lean_inc(v_asyncMode_1787_);
v___x_1788_ = lean_obj_once(&l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2, &l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2_once, _init_l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2);
v___x_1789_ = lean_box(0);
v___x_1790_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1788_, v___x_1786_, v_env_1785_, v_asyncMode_1787_, v___x_1789_);
lean_dec(v_asyncMode_1787_);
v___x_1791_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(v___x_1790_);
lean_dec(v___x_1790_);
v_sz_1792_ = lean_array_size(v___x_1791_);
v___x_1793_ = ((size_t)0ULL);
v___x_1794_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__1(v_sz_1792_, v___x_1793_, v___x_1791_);
v___x_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg___boxed(lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg(v_a_1796_);
lean_dec(v_a_1796_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls(lean_object* v_a_1799_, lean_object* v_a_1800_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = l_Lean_Compiler_LCNF_getLocalImpureDecls___redArg(v_a_1800_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalImpureDecls___boxed(lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_Compiler_LCNF_getLocalImpureDecls(v_a_1803_, v_a_1804_);
lean_dec(v_a_1804_);
lean_dec_ref(v_a_1803_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0(lean_object* v_00_u03b2_1807_, lean_object* v_m_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___redArg(v_m_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0___boxed(lean_object* v_00_u03b2_1810_, lean_object* v_m_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_PersistentHashMap_toArray___at___00Lean_Compiler_LCNF_getLocalImpureDecls_spec__0(v_00_u03b2_1810_, v_m_1811_);
lean_dec_ref(v_m_1811_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(lean_object* v_declName_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v___x_1816_; lean_object* v_env_1817_; uint8_t v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1816_ = lean_st_ref_get(v_a_1814_);
v_env_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc_ref(v_env_1817_);
lean_dec(v___x_1816_);
v___x_1818_ = 1;
v___x_1819_ = l_Lean_Compiler_LCNF_impureSigExt;
v___x_1820_ = l_Lean_Compiler_LCNF_getSigCore_x3f(v___x_1818_, v_env_1817_, v___x_1819_, v_declName_1813_);
v___x_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg___boxed(lean_object* v_declName_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_1822_, v_a_1823_);
lean_dec(v_a_1823_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f(lean_object* v_declName_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f___redArg(v_declName_1826_, v_a_1828_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureSignature_x3f___boxed(lean_object* v_declName_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Lean_Compiler_LCNF_getImpureSignature_x3f(v_declName_1831_, v_a_1832_, v_a_1833_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveBaseDeclCore(lean_object* v_env_1836_, lean_object* v_decl_1837_){
_start:
{
lean_object* v___x_1838_; lean_object* v_toEnvExtension_1839_; lean_object* v_asyncMode_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1838_ = l_Lean_Compiler_LCNF_baseExt;
v_toEnvExtension_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc_ref(v_toEnvExtension_1839_);
v_asyncMode_1840_ = lean_ctor_get(v_toEnvExtension_1839_, 2);
lean_inc(v_asyncMode_1840_);
lean_dec_ref(v_toEnvExtension_1839_);
v___x_1841_ = lean_box(0);
v___x_1842_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1838_, v_env_1836_, v_decl_1837_, v_asyncMode_1840_, v___x_1841_);
lean_dec(v_asyncMode_1840_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveMonoDeclCore(lean_object* v_env_1843_, lean_object* v_decl_1844_){
_start:
{
lean_object* v___x_1845_; lean_object* v_toEnvExtension_1846_; lean_object* v_asyncMode_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1845_ = l_Lean_Compiler_LCNF_monoExt;
v_toEnvExtension_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc_ref(v_toEnvExtension_1846_);
v_asyncMode_1847_ = lean_ctor_get(v_toEnvExtension_1846_, 2);
lean_inc(v_asyncMode_1847_);
lean_dec_ref(v_toEnvExtension_1846_);
v___x_1848_ = lean_box(0);
v___x_1849_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1845_, v_env_1843_, v_decl_1844_, v_asyncMode_1847_, v___x_1848_);
lean_dec(v_asyncMode_1847_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveImpureDeclCore___lam__0(lean_object* v_toSignature_1850_, lean_object* v_decl_1851_, lean_object* v_s_1852_){
_start:
{
lean_object* v_name_1853_; lean_object* v___x_1854_; 
v_name_1853_ = lean_ctor_get(v_toSignature_1850_, 0);
lean_inc(v_name_1853_);
lean_dec_ref(v_toSignature_1850_);
v___x_1854_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__1___redArg(v_s_1852_, v_name_1853_, v_decl_1851_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_saveImpureDeclCore(lean_object* v_env_1855_, lean_object* v_decl_1856_){
_start:
{
lean_object* v___x_1857_; lean_object* v_asyncMode_1858_; lean_object* v_toSignature_1859_; lean_object* v___x_1860_; lean_object* v_toEnvExtension_1861_; lean_object* v_asyncMode_1862_; lean_object* v___f_1863_; lean_object* v___x_1864_; lean_object* v_env_1865_; lean_object* v___x_1866_; 
v___x_1857_ = l_Lean_Compiler_LCNF_impureExt;
v_asyncMode_1858_ = lean_ctor_get(v___x_1857_, 2);
lean_inc(v_asyncMode_1858_);
v_toSignature_1859_ = lean_ctor_get(v_decl_1856_, 0);
lean_inc_ref(v_toSignature_1859_);
v___x_1860_ = l_Lean_Compiler_LCNF_impureSigExt;
v_toEnvExtension_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc_ref(v_toEnvExtension_1861_);
v_asyncMode_1862_ = lean_ctor_get(v_toEnvExtension_1861_, 2);
lean_inc(v_asyncMode_1862_);
lean_dec_ref(v_toEnvExtension_1861_);
lean_inc_ref(v_toSignature_1859_);
v___f_1863_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_saveImpureDeclCore___lam__0), 3, 2);
lean_closure_set(v___f_1863_, 0, v_toSignature_1859_);
lean_closure_set(v___f_1863_, 1, v_decl_1856_);
v___x_1864_ = lean_box(0);
v_env_1865_ = l_Lean_EnvExtension_modifyState___redArg(v___x_1857_, v_env_1855_, v___f_1863_, v_asyncMode_1858_, v___x_1864_);
lean_dec(v_asyncMode_1858_);
v___x_1866_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_1860_, v_env_1865_, v_toSignature_1859_, v_asyncMode_1862_, v___x_1864_);
lean_dec(v_asyncMode_1862_);
return v___x_1866_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0(void){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1867_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1(void){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0, &l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__0);
v___x_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
return v___x_1869_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2(void){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1, &l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__1);
v___x_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg(lean_object* v_decl_1872_, lean_object* v_a_1873_){
_start:
{
lean_object* v___x_1875_; lean_object* v_env_1876_; lean_object* v_nextMacroScope_1877_; lean_object* v_ngen_1878_; lean_object* v_auxDeclNGen_1879_; lean_object* v_traceState_1880_; lean_object* v_messages_1881_; lean_object* v_infoState_1882_; lean_object* v_snapshotTasks_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1895_; 
v___x_1875_ = lean_st_ref_take(v_a_1873_);
v_env_1876_ = lean_ctor_get(v___x_1875_, 0);
v_nextMacroScope_1877_ = lean_ctor_get(v___x_1875_, 1);
v_ngen_1878_ = lean_ctor_get(v___x_1875_, 2);
v_auxDeclNGen_1879_ = lean_ctor_get(v___x_1875_, 3);
v_traceState_1880_ = lean_ctor_get(v___x_1875_, 4);
v_messages_1881_ = lean_ctor_get(v___x_1875_, 6);
v_infoState_1882_ = lean_ctor_get(v___x_1875_, 7);
v_snapshotTasks_1883_ = lean_ctor_get(v___x_1875_, 8);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1895_ == 0)
{
lean_object* v_unused_1896_; 
v_unused_1896_ = lean_ctor_get(v___x_1875_, 5);
lean_dec(v_unused_1896_);
v___x_1885_ = v___x_1875_;
v_isShared_1886_ = v_isSharedCheck_1895_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_snapshotTasks_1883_);
lean_inc(v_infoState_1882_);
lean_inc(v_messages_1881_);
lean_inc(v_traceState_1880_);
lean_inc(v_auxDeclNGen_1879_);
lean_inc(v_ngen_1878_);
lean_inc(v_nextMacroScope_1877_);
lean_inc(v_env_1876_);
lean_dec(v___x_1875_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1895_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1887_ = l_Lean_Compiler_LCNF_saveBaseDeclCore(v_env_1876_, v_decl_1872_);
v___x_1888_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2, &l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 5, v___x_1888_);
lean_ctor_set(v___x_1885_, 0, v___x_1887_);
v___x_1890_ = v___x_1885_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_nextMacroScope_1877_);
lean_ctor_set(v_reuseFailAlloc_1894_, 2, v_ngen_1878_);
lean_ctor_set(v_reuseFailAlloc_1894_, 3, v_auxDeclNGen_1879_);
lean_ctor_set(v_reuseFailAlloc_1894_, 4, v_traceState_1880_);
lean_ctor_set(v_reuseFailAlloc_1894_, 5, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1894_, 6, v_messages_1881_);
lean_ctor_set(v_reuseFailAlloc_1894_, 7, v_infoState_1882_);
lean_ctor_set(v_reuseFailAlloc_1894_, 8, v_snapshotTasks_1883_);
v___x_1890_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = lean_st_ref_set(v_a_1873_, v___x_1890_);
v___x_1892_ = lean_box(0);
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
return v___x_1893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg___boxed(lean_object* v_decl_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(v_decl_1897_, v_a_1898_);
lean_dec(v_a_1898_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase(lean_object* v_decl_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(v_decl_1901_, v_a_1903_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___boxed(lean_object* v_decl_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_Compiler_LCNF_Decl_saveBase(v_decl_1906_, v_a_1907_, v_a_1908_);
lean_dec(v_a_1908_);
lean_dec_ref(v_a_1907_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object* v_decl_1911_, lean_object* v_a_1912_){
_start:
{
lean_object* v___x_1914_; lean_object* v_env_1915_; lean_object* v_nextMacroScope_1916_; lean_object* v_ngen_1917_; lean_object* v_auxDeclNGen_1918_; lean_object* v_traceState_1919_; lean_object* v_messages_1920_; lean_object* v_infoState_1921_; lean_object* v_snapshotTasks_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1934_; 
v___x_1914_ = lean_st_ref_take(v_a_1912_);
v_env_1915_ = lean_ctor_get(v___x_1914_, 0);
v_nextMacroScope_1916_ = lean_ctor_get(v___x_1914_, 1);
v_ngen_1917_ = lean_ctor_get(v___x_1914_, 2);
v_auxDeclNGen_1918_ = lean_ctor_get(v___x_1914_, 3);
v_traceState_1919_ = lean_ctor_get(v___x_1914_, 4);
v_messages_1920_ = lean_ctor_get(v___x_1914_, 6);
v_infoState_1921_ = lean_ctor_get(v___x_1914_, 7);
v_snapshotTasks_1922_ = lean_ctor_get(v___x_1914_, 8);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; 
v_unused_1935_ = lean_ctor_get(v___x_1914_, 5);
lean_dec(v_unused_1935_);
v___x_1924_ = v___x_1914_;
v_isShared_1925_ = v_isSharedCheck_1934_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_snapshotTasks_1922_);
lean_inc(v_infoState_1921_);
lean_inc(v_messages_1920_);
lean_inc(v_traceState_1919_);
lean_inc(v_auxDeclNGen_1918_);
lean_inc(v_ngen_1917_);
lean_inc(v_nextMacroScope_1916_);
lean_inc(v_env_1915_);
lean_dec(v___x_1914_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1934_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1929_; 
v___x_1926_ = l_Lean_Compiler_LCNF_saveMonoDeclCore(v_env_1915_, v_decl_1911_);
v___x_1927_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2, &l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 5, v___x_1927_);
lean_ctor_set(v___x_1924_, 0, v___x_1926_);
v___x_1929_ = v___x_1924_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_1933_, 1, v_nextMacroScope_1916_);
lean_ctor_set(v_reuseFailAlloc_1933_, 2, v_ngen_1917_);
lean_ctor_set(v_reuseFailAlloc_1933_, 3, v_auxDeclNGen_1918_);
lean_ctor_set(v_reuseFailAlloc_1933_, 4, v_traceState_1919_);
lean_ctor_set(v_reuseFailAlloc_1933_, 5, v___x_1927_);
lean_ctor_set(v_reuseFailAlloc_1933_, 6, v_messages_1920_);
lean_ctor_set(v_reuseFailAlloc_1933_, 7, v_infoState_1921_);
lean_ctor_set(v_reuseFailAlloc_1933_, 8, v_snapshotTasks_1922_);
v___x_1929_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = lean_st_ref_set(v_a_1912_, v___x_1929_);
v___x_1931_ = lean_box(0);
v___x_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
return v___x_1932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg___boxed(lean_object* v_decl_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v_decl_1936_, v_a_1937_);
lean_dec(v_a_1937_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono(lean_object* v_decl_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v_decl_1940_, v_a_1942_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___boxed(lean_object* v_decl_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_Compiler_LCNF_Decl_saveMono(v_decl_1945_, v_a_1946_, v_a_1947_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(lean_object* v_decl_1950_, lean_object* v_a_1951_){
_start:
{
lean_object* v___x_1953_; lean_object* v_env_1954_; lean_object* v_nextMacroScope_1955_; lean_object* v_ngen_1956_; lean_object* v_auxDeclNGen_1957_; lean_object* v_traceState_1958_; lean_object* v_messages_1959_; lean_object* v_infoState_1960_; lean_object* v_snapshotTasks_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1973_; 
v___x_1953_ = lean_st_ref_take(v_a_1951_);
v_env_1954_ = lean_ctor_get(v___x_1953_, 0);
v_nextMacroScope_1955_ = lean_ctor_get(v___x_1953_, 1);
v_ngen_1956_ = lean_ctor_get(v___x_1953_, 2);
v_auxDeclNGen_1957_ = lean_ctor_get(v___x_1953_, 3);
v_traceState_1958_ = lean_ctor_get(v___x_1953_, 4);
v_messages_1959_ = lean_ctor_get(v___x_1953_, 6);
v_infoState_1960_ = lean_ctor_get(v___x_1953_, 7);
v_snapshotTasks_1961_ = lean_ctor_get(v___x_1953_, 8);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1973_ == 0)
{
lean_object* v_unused_1974_; 
v_unused_1974_ = lean_ctor_get(v___x_1953_, 5);
lean_dec(v_unused_1974_);
v___x_1963_ = v___x_1953_;
v_isShared_1964_ = v_isSharedCheck_1973_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_snapshotTasks_1961_);
lean_inc(v_infoState_1960_);
lean_inc(v_messages_1959_);
lean_inc(v_traceState_1958_);
lean_inc(v_auxDeclNGen_1957_);
lean_inc(v_ngen_1956_);
lean_inc(v_nextMacroScope_1955_);
lean_inc(v_env_1954_);
lean_dec(v___x_1953_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1973_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1968_; 
v___x_1965_ = l_Lean_Compiler_LCNF_saveImpureDeclCore(v_env_1954_, v_decl_1950_);
v___x_1966_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2, &l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_Decl_saveBase___redArg___closed__2);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 5, v___x_1966_);
lean_ctor_set(v___x_1963_, 0, v___x_1965_);
v___x_1968_ = v___x_1963_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_nextMacroScope_1955_);
lean_ctor_set(v_reuseFailAlloc_1972_, 2, v_ngen_1956_);
lean_ctor_set(v_reuseFailAlloc_1972_, 3, v_auxDeclNGen_1957_);
lean_ctor_set(v_reuseFailAlloc_1972_, 4, v_traceState_1958_);
lean_ctor_set(v_reuseFailAlloc_1972_, 5, v___x_1966_);
lean_ctor_set(v_reuseFailAlloc_1972_, 6, v_messages_1959_);
lean_ctor_set(v_reuseFailAlloc_1972_, 7, v_infoState_1960_);
lean_ctor_set(v_reuseFailAlloc_1972_, 8, v_snapshotTasks_1961_);
v___x_1968_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = lean_st_ref_set(v_a_1951_, v___x_1968_);
v___x_1970_ = lean_box(0);
v___x_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
return v___x_1971_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg___boxed(lean_object* v_decl_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_decl_1975_, v_a_1976_);
lean_dec(v_a_1976_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure(lean_object* v_decl_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_decl_1979_, v_a_1981_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___boxed(lean_object* v_decl_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Lean_Compiler_LCNF_Decl_saveImpure(v_decl_1984_, v_a_1985_, v_a_1986_);
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__0(lean_object* v_decl_1989_, lean_object* v_h_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v___x_1996_; 
v___x_1996_ = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(v_decl_1989_, v___y_1994_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__0___boxed(lean_object* v_decl_1997_, lean_object* v_h_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Lean_Compiler_LCNF_Decl_save___lam__0(v_decl_1997_, v_h_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__1(lean_object* v_decl_2005_, lean_object* v_h_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v_decl_2005_, v___y_2010_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__1___boxed(lean_object* v_decl_2013_, lean_object* v_h_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_Lean_Compiler_LCNF_Decl_save___lam__1(v_decl_2013_, v_h_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__2(lean_object* v_decl_2021_, lean_object* v_h_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_decl_2021_, v___y_2026_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___lam__2___boxed(lean_object* v_decl_2029_, lean_object* v_h_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Lean_Compiler_LCNF_Decl_save___lam__2(v_decl_2029_, v_h_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
return v_res_2036_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_save___closed__0(void){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = l_instMonadEIO(lean_box(0));
return v___x_2037_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_save___closed__1(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_save___closed__0, &l_Lean_Compiler_LCNF_Decl_save___closed__0_once, _init_l_Lean_Compiler_LCNF_Decl_save___closed__0);
v___x_2039_ = l_StateRefT_x27_instMonad___redArg(v___x_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save(uint8_t v_pu_2042_, lean_object* v_decl_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_){
_start:
{
lean_object* v___x_2049_; lean_object* v_toApplicative_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2104_; 
v___x_2049_ = lean_obj_once(&l_Lean_Compiler_LCNF_Decl_save___closed__1, &l_Lean_Compiler_LCNF_Decl_save___closed__1_once, _init_l_Lean_Compiler_LCNF_Decl_save___closed__1);
v_toApplicative_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2104_ == 0)
{
lean_object* v_unused_2105_; 
v_unused_2105_ = lean_ctor_get(v___x_2049_, 1);
lean_dec(v_unused_2105_);
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2104_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_toApplicative_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2104_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v_toFunctor_2054_; lean_object* v_toSeq_2055_; lean_object* v_toSeqLeft_2056_; lean_object* v_toSeqRight_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2102_; 
v_toFunctor_2054_ = lean_ctor_get(v_toApplicative_2050_, 0);
v_toSeq_2055_ = lean_ctor_get(v_toApplicative_2050_, 2);
v_toSeqLeft_2056_ = lean_ctor_get(v_toApplicative_2050_, 3);
v_toSeqRight_2057_ = lean_ctor_get(v_toApplicative_2050_, 4);
v_isSharedCheck_2102_ = !lean_is_exclusive(v_toApplicative_2050_);
if (v_isSharedCheck_2102_ == 0)
{
lean_object* v_unused_2103_; 
v_unused_2103_ = lean_ctor_get(v_toApplicative_2050_, 1);
lean_dec(v_unused_2103_);
v___x_2059_ = v_toApplicative_2050_;
v_isShared_2060_ = v_isSharedCheck_2102_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_toSeqRight_2057_);
lean_inc(v_toSeqLeft_2056_);
lean_inc(v_toSeq_2055_);
lean_inc(v_toFunctor_2054_);
lean_dec(v_toApplicative_2050_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2102_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___f_2061_; lean_object* v___f_2062_; lean_object* v___f_2063_; lean_object* v___f_2064_; lean_object* v___x_2065_; lean_object* v___f_2066_; lean_object* v___f_2067_; lean_object* v___f_2068_; lean_object* v___x_2070_; 
v___f_2061_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_save___closed__2));
v___f_2062_ = ((lean_object*)(l_Lean_Compiler_LCNF_Decl_save___closed__3));
lean_inc_ref(v_toFunctor_2054_);
v___f_2063_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2063_, 0, v_toFunctor_2054_);
v___f_2064_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2064_, 0, v_toFunctor_2054_);
v___x_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___f_2063_);
lean_ctor_set(v___x_2065_, 1, v___f_2064_);
v___f_2066_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2066_, 0, v_toSeqRight_2057_);
v___f_2067_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2067_, 0, v_toSeqLeft_2056_);
v___f_2068_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2068_, 0, v_toSeq_2055_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 4, v___f_2066_);
lean_ctor_set(v___x_2059_, 3, v___f_2067_);
lean_ctor_set(v___x_2059_, 2, v___f_2068_);
lean_ctor_set(v___x_2059_, 1, v___f_2061_);
lean_ctor_set(v___x_2059_, 0, v___x_2065_);
v___x_2070_ = v___x_2059_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v___f_2061_);
lean_ctor_set(v_reuseFailAlloc_2101_, 2, v___f_2068_);
lean_ctor_set(v_reuseFailAlloc_2101_, 3, v___f_2067_);
lean_ctor_set(v_reuseFailAlloc_2101_, 4, v___f_2066_);
v___x_2070_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2072_; 
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 1, v___f_2062_);
lean_ctor_set(v___x_2052_, 0, v___x_2070_);
v___x_2072_ = v___x_2052_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2070_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v___f_2062_);
v___x_2072_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = l_StateRefT_x27_instMonad___redArg(v___x_2072_);
v___x_2074_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_2044_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___f_2078_; uint8_t v___x_2079_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2075_);
lean_dec_ref(v___x_2074_);
v___x_2076_ = lean_box(0);
v___x_2077_ = l_instInhabitedOfMonad___redArg(v___x_2073_, v___x_2076_);
v___f_2078_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2078_, 0, v___x_2077_);
v___x_2079_ = lean_unbox(v_a_2075_);
switch(v___x_2079_)
{
case 0:
{
lean_object* v___f_2080_; uint8_t v___x_2081_; lean_object* v___x_380__overap_2082_; lean_object* v___x_2083_; 
v___f_2080_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_save___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2080_, 0, v_decl_2043_);
v___x_2081_ = lean_unbox(v_a_2075_);
lean_dec(v_a_2075_);
v___x_380__overap_2082_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___f_2078_, v___x_2081_, v_pu_2042_, v___f_2080_);
lean_inc(v_a_2047_);
lean_inc_ref(v_a_2046_);
lean_inc(v_a_2045_);
lean_inc_ref(v_a_2044_);
v___x_2083_ = lean_apply_5(v___x_380__overap_2082_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, lean_box(0));
return v___x_2083_;
}
case 1:
{
lean_object* v___f_2084_; uint8_t v___x_2085_; lean_object* v___x_398__overap_2086_; lean_object* v___x_2087_; 
v___f_2084_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_save___lam__1___boxed), 7, 1);
lean_closure_set(v___f_2084_, 0, v_decl_2043_);
v___x_2085_ = lean_unbox(v_a_2075_);
lean_dec(v_a_2075_);
v___x_398__overap_2086_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___f_2078_, v___x_2085_, v_pu_2042_, v___f_2084_);
lean_inc(v_a_2047_);
lean_inc_ref(v_a_2046_);
lean_inc(v_a_2045_);
lean_inc_ref(v_a_2044_);
v___x_2087_ = lean_apply_5(v___x_398__overap_2086_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, lean_box(0));
return v___x_2087_;
}
default: 
{
lean_object* v___f_2088_; uint8_t v___x_2089_; lean_object* v___x_416__overap_2090_; lean_object* v___x_2091_; 
v___f_2088_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_save___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2088_, 0, v_decl_2043_);
v___x_2089_ = lean_unbox(v_a_2075_);
lean_dec(v_a_2075_);
v___x_416__overap_2090_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(v___f_2078_, v___x_2089_, v_pu_2042_, v___f_2088_);
lean_inc(v_a_2047_);
lean_inc_ref(v_a_2046_);
lean_inc(v_a_2045_);
lean_inc_ref(v_a_2044_);
v___x_2091_ = lean_apply_5(v___x_416__overap_2090_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, lean_box(0));
return v___x_2091_;
}
}
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
lean_dec_ref(v___x_2073_);
lean_dec_ref(v_decl_2043_);
v_a_2092_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2074_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2074_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_save___boxed(lean_object* v_pu_2106_, lean_object* v_decl_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
uint8_t v_pu_boxed_2113_; lean_object* v_res_2114_; 
v_pu_boxed_2113_ = lean_unbox(v_pu_2106_);
v_res_2114_ = l_Lean_Compiler_LCNF_Decl_save(v_pu_boxed_2113_, v_decl_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
return v_res_2114_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2115_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__0);
v___x_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
return v___x_2117_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2118_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1);
v___x_2119_ = lean_unsigned_to_nat(0u);
v___x_2120_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
lean_ctor_set(v___x_2120_, 2, v___x_2119_);
lean_ctor_set(v___x_2120_, 3, v___x_2118_);
lean_ctor_set(v___x_2120_, 4, v___x_2118_);
lean_ctor_set(v___x_2120_, 5, v___x_2118_);
lean_ctor_set(v___x_2120_, 6, v___x_2118_);
lean_ctor_set(v___x_2120_, 7, v___x_2118_);
lean_ctor_set(v___x_2120_, 8, v___x_2118_);
return v___x_2120_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2121_ = lean_unsigned_to_nat(32u);
v___x_2122_ = lean_mk_empty_array_with_capacity(v___x_2121_);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
return v___x_2123_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2124_ = ((size_t)5ULL);
v___x_2125_ = lean_unsigned_to_nat(0u);
v___x_2126_ = lean_unsigned_to_nat(32u);
v___x_2127_ = lean_mk_empty_array_with_capacity(v___x_2126_);
v___x_2128_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__3);
v___x_2129_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2129_, 0, v___x_2128_);
lean_ctor_set(v___x_2129_, 1, v___x_2127_);
lean_ctor_set(v___x_2129_, 2, v___x_2125_);
lean_ctor_set(v___x_2129_, 3, v___x_2125_);
lean_ctor_set_usize(v___x_2129_, 4, v___x_2124_);
return v___x_2129_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2130_ = lean_box(1);
v___x_2131_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__4);
v___x_2132_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__1);
v___x_2133_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
lean_ctor_set(v___x_2133_, 1, v___x_2131_);
lean_ctor_set(v___x_2133_, 2, v___x_2130_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0(lean_object* v_msgData_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2138_; lean_object* v_env_2139_; lean_object* v_options_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2138_ = lean_st_ref_get(v___y_2136_);
v_env_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc_ref(v_env_2139_);
lean_dec(v___x_2138_);
v_options_2140_ = lean_ctor_get(v___y_2135_, 2);
v___x_2141_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__2);
v___x_2142_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_2140_);
v___x_2143_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2143_, 0, v_env_2139_);
lean_ctor_set(v___x_2143_, 1, v___x_2141_);
lean_ctor_set(v___x_2143_, 2, v___x_2142_);
lean_ctor_set(v___x_2143_, 3, v_options_2140_);
v___x_2144_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2143_);
lean_ctor_set(v___x_2144_, 1, v_msgData_2134_);
v___x_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0(v_msgData_2146_, v___y_2147_, v___y_2148_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(lean_object* v_msg_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v_ref_2155_; lean_object* v___x_2156_; lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2165_; 
v_ref_2155_ = lean_ctor_get(v___y_2152_, 5);
v___x_2156_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0_spec__0(v_msg_2151_, v___y_2152_, v___y_2153_);
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2159_ = v___x_2156_;
v_isShared_2160_ = v_isSharedCheck_2165_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2156_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2165_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2161_; lean_object* v___x_2163_; 
lean_inc(v_ref_2155_);
v___x_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2161_, 0, v_ref_2155_);
lean_ctor_set(v___x_2161_, 1, v_a_2157_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set_tag(v___x_2159_, 1);
lean_ctor_set(v___x_2159_, 0, v___x_2161_);
v___x_2163_ = v___x_2159_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg___boxed(lean_object* v_msg_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(v_msg_2166_, v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
return v_res_2170_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1(void){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = ((lean_object*)(l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__0));
v___x_2173_ = l_Lean_stringToMessageData(v___x_2172_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f(lean_object* v_declName_2174_, uint8_t v_phase_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
switch(v_phase_2175_)
{
case 0:
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Lean_Compiler_LCNF_getBaseDecl_x3f___redArg(v_declName_2174_, v_a_2177_);
return v___x_2179_;
}
case 1:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_2174_, v_a_2177_);
return v___x_2180_;
}
default: 
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
lean_dec(v_declName_2174_);
v___x_2181_ = lean_obj_once(&l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1, &l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1_once, _init_l_Lean_Compiler_LCNF_getDeclAt_x3f___closed__1);
v___x_2182_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(v___x_2181_, v_a_2176_, v_a_2177_);
return v___x_2182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclAt_x3f___boxed(lean_object* v_declName_2183_, lean_object* v_phase_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_){
_start:
{
uint8_t v_phase_boxed_2188_; lean_object* v_res_2189_; 
v_phase_boxed_2188_ = lean_unbox(v_phase_2184_);
v_res_2189_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_2183_, v_phase_boxed_2188_, v_a_2185_, v_a_2186_);
lean_dec(v_a_2186_);
lean_dec_ref(v_a_2185_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0(lean_object* v_00_u03b1_2190_, lean_object* v_msg_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___redArg(v_msg_2191_, v___y_2192_, v___y_2193_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0___boxed(lean_object* v_00_u03b1_2196_, lean_object* v_msg_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_getDeclAt_x3f_spec__0(v_00_u03b1_2196_, v_msg_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg(lean_object* v_declName_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_2203_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; uint8_t v___x_2209_; lean_object* v___x_2210_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2208_);
lean_dec_ref(v___x_2207_);
v___x_2209_ = lean_unbox(v_a_2208_);
v___x_2210_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_2202_, v___x_2209_, v_a_2204_, v_a_2205_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2234_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2213_ = v___x_2210_;
v_isShared_2214_ = v_isSharedCheck_2234_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2210_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2234_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
if (lean_obj_tag(v_a_2211_) == 1)
{
lean_object* v_val_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2229_; 
v_val_2215_ = lean_ctor_get(v_a_2211_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_a_2211_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2217_ = v_a_2211_;
v_isShared_2218_ = v_isSharedCheck_2229_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_val_2215_);
lean_dec(v_a_2211_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2229_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
uint8_t v___x_2219_; uint8_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2219_ = lean_unbox(v_a_2208_);
lean_dec(v_a_2208_);
v___x_2220_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_2219_);
v___x_2221_ = lean_box(v___x_2220_);
v___x_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
lean_ctor_set(v___x_2222_, 1, v_val_2215_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 0, v___x_2222_);
v___x_2224_ = v___x_2217_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2226_; 
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 0, v___x_2224_);
v___x_2226_ = v___x_2213_;
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
else
{
lean_object* v___x_2230_; lean_object* v___x_2232_; 
lean_dec(v_a_2211_);
lean_dec(v_a_2208_);
v___x_2230_ = lean_box(0);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 0, v___x_2230_);
v___x_2232_ = v___x_2213_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2230_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_dec(v_a_2208_);
v_a_2235_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2210_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2210_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec(v_declName_2202_);
v_a_2243_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2207_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2207_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg___boxed(lean_object* v_declName_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(v_declName_2251_, v_a_2252_, v_a_2253_, v_a_2254_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
lean_dec_ref(v_a_2252_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f(lean_object* v_declName_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_2258_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; uint8_t v___x_2265_; lean_object* v___x_2266_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_a_2264_);
lean_dec_ref(v___x_2263_);
v___x_2265_ = lean_unbox(v_a_2264_);
v___x_2266_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(v_declName_2257_, v___x_2265_, v_a_2260_, v_a_2261_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2290_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2269_ = v___x_2266_;
v_isShared_2270_ = v_isSharedCheck_2290_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2266_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2290_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
if (lean_obj_tag(v_a_2267_) == 1)
{
lean_object* v_val_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2285_; 
v_val_2271_ = lean_ctor_get(v_a_2267_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v_a_2267_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2273_ = v_a_2267_;
v_isShared_2274_ = v_isSharedCheck_2285_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_val_2271_);
lean_dec(v_a_2267_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2285_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
uint8_t v___x_2275_; uint8_t v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2280_; 
v___x_2275_ = lean_unbox(v_a_2264_);
lean_dec(v_a_2264_);
v___x_2276_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_2275_);
v___x_2277_ = lean_box(v___x_2276_);
v___x_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2277_);
lean_ctor_set(v___x_2278_, 1, v_val_2271_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v___x_2278_);
v___x_2280_ = v___x_2273_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2278_);
v___x_2280_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
lean_object* v___x_2282_; 
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 0, v___x_2280_);
v___x_2282_ = v___x_2269_;
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
lean_object* v___x_2286_; lean_object* v___x_2288_; 
lean_dec(v_a_2267_);
lean_dec(v_a_2264_);
v___x_2286_ = lean_box(0);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 0, v___x_2286_);
v___x_2288_ = v___x_2269_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec(v_a_2264_);
v_a_2291_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2266_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2266_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec(v_declName_2257_);
v_a_2299_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2263_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2263_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___boxed(lean_object* v_declName_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_Compiler_LCNF_getDecl_x3f(v_declName_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_);
lean_dec(v_a_2311_);
lean_dec_ref(v_a_2310_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(lean_object* v_declName_2314_, uint8_t v_phase_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = lean_obj_once(&l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2, &l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2_once, _init_l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__2);
switch(v_phase_2315_)
{
case 0:
{
lean_object* v___x_2319_; lean_object* v_env_2320_; lean_object* v___x_2321_; lean_object* v_toEnvExtension_2322_; lean_object* v_asyncMode_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2319_ = lean_st_ref_get(v_a_2316_);
v_env_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc_ref(v_env_2320_);
lean_dec(v___x_2319_);
v___x_2321_ = l_Lean_Compiler_LCNF_baseExt;
v_toEnvExtension_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc_ref(v_toEnvExtension_2322_);
v_asyncMode_2323_ = lean_ctor_get(v_toEnvExtension_2322_, 2);
lean_inc(v_asyncMode_2323_);
lean_dec_ref(v_toEnvExtension_2322_);
v___x_2324_ = lean_box(0);
v___x_2325_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2318_, v___x_2321_, v_env_2320_, v_asyncMode_2323_, v___x_2324_);
lean_dec(v_asyncMode_2323_);
v___x_2326_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_2325_, v_declName_2314_);
v___x_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
return v___x_2327_;
}
case 1:
{
lean_object* v___x_2328_; lean_object* v_env_2329_; lean_object* v___x_2330_; lean_object* v_toEnvExtension_2331_; lean_object* v_asyncMode_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2328_ = lean_st_ref_get(v_a_2316_);
v_env_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc_ref(v_env_2329_);
lean_dec(v___x_2328_);
v___x_2330_ = l_Lean_Compiler_LCNF_monoExt;
v_toEnvExtension_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc_ref(v_toEnvExtension_2331_);
v_asyncMode_2332_ = lean_ctor_get(v_toEnvExtension_2331_, 2);
lean_inc(v_asyncMode_2332_);
lean_dec_ref(v_toEnvExtension_2331_);
v___x_2333_ = lean_box(0);
v___x_2334_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2318_, v___x_2330_, v_env_2329_, v_asyncMode_2332_, v___x_2333_);
lean_dec(v_asyncMode_2332_);
v___x_2335_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_2334_, v_declName_2314_);
v___x_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2335_);
return v___x_2336_;
}
default: 
{
lean_object* v___x_2337_; lean_object* v_env_2338_; lean_object* v___x_2339_; lean_object* v_asyncMode_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2337_ = lean_st_ref_get(v_a_2316_);
v_env_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc_ref(v_env_2338_);
lean_dec(v___x_2337_);
v___x_2339_ = l_Lean_Compiler_LCNF_impureExt;
v_asyncMode_2340_ = lean_ctor_get(v___x_2339_, 2);
lean_inc(v_asyncMode_2340_);
v___x_2341_ = lean_box(0);
v___x_2342_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2318_, v___x_2339_, v_env_2338_, v_asyncMode_2340_, v___x_2341_);
lean_dec(v_asyncMode_2340_);
v___x_2343_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_getDeclCore_x3f_spec__0___redArg(v___x_2342_, v_declName_2314_);
v___x_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
return v___x_2344_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg___boxed(lean_object* v_declName_2345_, lean_object* v_phase_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
uint8_t v_phase_boxed_2349_; lean_object* v_res_2350_; 
v_phase_boxed_2349_ = lean_unbox(v_phase_2346_);
v_res_2350_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_declName_2345_, v_phase_boxed_2349_, v_a_2347_);
lean_dec(v_a_2347_);
lean_dec(v_declName_2345_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f(lean_object* v_declName_2351_, uint8_t v_phase_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_declName_2351_, v_phase_2352_, v_a_2356_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___boxed(lean_object* v_declName_2359_, lean_object* v_phase_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
uint8_t v_phase_boxed_2366_; lean_object* v_res_2367_; 
v_phase_boxed_2366_ = lean_unbox(v_phase_2360_);
v_res_2367_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f(v_declName_2359_, v_phase_boxed_2366_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_declName_2359_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f___redArg(lean_object* v_declName_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_2369_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v_a_2373_; uint8_t v___x_2374_; lean_object* v___x_2375_; lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2399_; 
v_a_2373_ = lean_ctor_get(v___x_2372_, 0);
lean_inc(v_a_2373_);
lean_dec_ref(v___x_2372_);
v___x_2374_ = lean_unbox(v_a_2373_);
v___x_2375_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_declName_2368_, v___x_2374_, v_a_2370_);
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2378_ = v___x_2375_;
v_isShared_2379_ = v_isSharedCheck_2399_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2375_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2399_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
if (lean_obj_tag(v_a_2376_) == 1)
{
lean_object* v_val_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2394_; 
v_val_2380_ = lean_ctor_get(v_a_2376_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_a_2376_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2382_ = v_a_2376_;
v_isShared_2383_ = v_isSharedCheck_2394_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_val_2380_);
lean_dec(v_a_2376_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2394_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
uint8_t v___x_2384_; uint8_t v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2389_; 
v___x_2384_ = lean_unbox(v_a_2373_);
lean_dec(v_a_2373_);
v___x_2385_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_2384_);
v___x_2386_ = lean_box(v___x_2385_);
v___x_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
lean_ctor_set(v___x_2387_, 1, v_val_2380_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2387_);
v___x_2389_ = v___x_2382_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2391_; 
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2389_);
v___x_2391_ = v___x_2378_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
else
{
lean_object* v___x_2395_; lean_object* v___x_2397_; 
lean_dec(v_a_2376_);
lean_dec(v_a_2373_);
v___x_2395_ = lean_box(0);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2395_);
v___x_2397_ = v___x_2378_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
v_a_2400_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2372_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2372_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f___redArg___boxed(lean_object* v_declName_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Lean_Compiler_LCNF_getLocalDecl_x3f___redArg(v_declName_2408_, v_a_2409_, v_a_2410_);
lean_dec(v_a_2410_);
lean_dec_ref(v_a_2409_);
lean_dec(v_declName_2408_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f(lean_object* v_declName_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_2414_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; uint8_t v___x_2421_; lean_object* v___x_2422_; lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2446_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_a_2420_);
lean_dec_ref(v___x_2419_);
v___x_2421_ = lean_unbox(v_a_2420_);
v___x_2422_ = l_Lean_Compiler_LCNF_getLocalDeclAt_x3f___redArg(v_declName_2413_, v___x_2421_, v_a_2417_);
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2425_ = v___x_2422_;
v_isShared_2426_ = v_isSharedCheck_2446_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2422_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2446_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
if (lean_obj_tag(v_a_2423_) == 1)
{
lean_object* v_val_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2441_; 
v_val_2427_ = lean_ctor_get(v_a_2423_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_a_2423_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2429_ = v_a_2423_;
v_isShared_2430_ = v_isSharedCheck_2441_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_val_2427_);
lean_dec(v_a_2423_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2441_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
uint8_t v___x_2431_; uint8_t v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2431_ = lean_unbox(v_a_2420_);
lean_dec(v_a_2420_);
v___x_2432_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_2431_);
v___x_2433_ = lean_box(v___x_2432_);
v___x_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
lean_ctor_set(v___x_2434_, 1, v_val_2427_);
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 0, v___x_2434_);
v___x_2436_ = v___x_2429_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2438_; 
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 0, v___x_2436_);
v___x_2438_ = v___x_2425_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2436_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
else
{
lean_object* v___x_2442_; lean_object* v___x_2444_; 
lean_dec(v_a_2423_);
lean_dec(v_a_2420_);
v___x_2442_ = lean_box(0);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 0, v___x_2442_);
v___x_2444_ = v___x_2425_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2442_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
else
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2454_; 
v_a_2447_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2449_ = v___x_2419_;
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2419_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLocalDecl_x3f___boxed(lean_object* v_declName_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Lean_Compiler_LCNF_getLocalDecl_x3f(v_declName_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
lean_dec(v_a_2459_);
lean_dec_ref(v_a_2458_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_declName_2455_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2463_; 
v___x_2463_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2____boxed(lean_object* v_a_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2_();
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_recordFinalImpureDecl___lam__0(lean_object* v_name_2466_, lean_object* v_s_2467_){
_start:
{
lean_object* v_fst_2468_; lean_object* v_snd_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2478_; 
v_fst_2468_ = lean_ctor_get(v_s_2467_, 0);
v_snd_2469_ = lean_ctor_get(v_s_2467_, 1);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_s_2467_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2471_ = v_s_2467_;
v_isShared_2472_ = v_isSharedCheck_2478_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_snd_2469_);
lean_inc(v_fst_2468_);
lean_dec(v_s_2467_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2478_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
lean_inc(v_name_2466_);
v___x_2473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2473_, 0, v_name_2466_);
lean_ctor_set(v___x_2473_, 1, v_fst_2468_);
v___x_2474_ = l_Lean_NameSet_insert(v_snd_2469_, v_name_2466_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 1, v___x_2474_);
lean_ctor_set(v___x_2471_, 0, v___x_2473_);
v___x_2476_ = v___x_2471_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_recordFinalImpureDecl(lean_object* v_env_2479_, lean_object* v_name_2480_){
_start:
{
lean_object* v___x_2481_; lean_object* v_asyncMode_2482_; lean_object* v___f_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2481_ = l_Lean_Compiler_LCNF_declOrderExt;
v_asyncMode_2482_ = lean_ctor_get(v___x_2481_, 2);
lean_inc(v_asyncMode_2482_);
v___f_2483_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_recordFinalImpureDecl___lam__0), 2, 1);
lean_closure_set(v___f_2483_, 0, v_name_2480_);
v___x_2484_ = lean_box(0);
v___x_2485_ = l_Lean_EnvExtension_modifyState___redArg(v___x_2481_, v_env_2479_, v___f_2483_, v_asyncMode_2482_, v___x_2484_);
lean_dec(v_asyncMode_2482_);
return v___x_2485_;
}
}
static lean_object* _init_l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7(void){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2493_ = ((lean_object*)(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__1));
v___x_2494_ = ((lean_object*)(l_Lean_Compiler_LCNF_getDeclCore_x3f___closed__0));
v___x_2495_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2494_, v___x_2493_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1(lean_object* v_msg_2496_){
_start:
{
lean_object* v___f_2497_; lean_object* v___f_2498_; lean_object* v___f_2499_; lean_object* v___f_2500_; lean_object* v___f_2501_; lean_object* v___f_2502_; lean_object* v___f_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___f_2497_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__0));
v___f_2498_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__1));
v___f_2499_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__2));
v___f_2500_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__3));
v___f_2501_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__4));
v___f_2502_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__5));
v___f_2503_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__6));
v___x_2504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___f_2497_);
lean_ctor_set(v___x_2504_, 1, v___f_2498_);
v___x_2505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2504_);
lean_ctor_set(v___x_2505_, 1, v___f_2499_);
lean_ctor_set(v___x_2505_, 2, v___f_2500_);
lean_ctor_set(v___x_2505_, 3, v___f_2501_);
lean_ctor_set(v___x_2505_, 4, v___f_2502_);
v___x_2506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
lean_ctor_set(v___x_2506_, 1, v___f_2503_);
v___x_2507_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7, &l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7_once, _init_l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7);
v___x_2508_ = lean_unsigned_to_nat(0u);
v___x_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2507_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2509_);
v___x_2511_ = l_instInhabitedOfMonad___redArg(v___x_2506_, v___x_2510_);
v___x_2512_ = lean_panic_fn(v___x_2511_, v_msg_2496_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__5(lean_object* v_msg_2513_){
_start:
{
lean_object* v___f_2514_; lean_object* v___f_2515_; lean_object* v___f_2516_; lean_object* v___f_2517_; lean_object* v___f_2518_; lean_object* v___f_2519_; lean_object* v___f_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___f_2514_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__0));
v___f_2515_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__1));
v___f_2516_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__2));
v___f_2517_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__3));
v___f_2518_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__4));
v___f_2519_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__5));
v___f_2520_ = ((lean_object*)(l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__6));
v___x_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___f_2514_);
lean_ctor_set(v___x_2521_, 1, v___f_2515_);
v___x_2522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
lean_ctor_set(v___x_2522_, 1, v___f_2516_);
lean_ctor_set(v___x_2522_, 2, v___f_2517_);
lean_ctor_set(v___x_2522_, 3, v___f_2518_);
lean_ctor_set(v___x_2522_, 4, v___f_2519_);
v___x_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2522_);
lean_ctor_set(v___x_2523_, 1, v___f_2520_);
v___x_2524_ = lean_obj_once(&l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7, &l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7_once, _init_l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1___closed__7);
v___x_2525_ = l_instInhabitedOfMonad___redArg(v___x_2523_, v___x_2524_);
v___x_2526_ = lean_panic_fn(v___x_2525_, v_msg_2513_);
return v___x_2526_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(lean_object* v_a_2527_, lean_object* v_x_2528_){
_start:
{
if (lean_obj_tag(v_x_2528_) == 0)
{
uint8_t v___x_2529_; 
v___x_2529_ = 0;
return v___x_2529_;
}
else
{
lean_object* v_key_2530_; lean_object* v_tail_2531_; uint8_t v___x_2532_; 
v_key_2530_ = lean_ctor_get(v_x_2528_, 0);
v_tail_2531_ = lean_ctor_get(v_x_2528_, 2);
v___x_2532_ = lean_name_eq(v_key_2530_, v_a_2527_);
if (v___x_2532_ == 0)
{
v_x_2528_ = v_tail_2531_;
goto _start;
}
else
{
return v___x_2532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg___boxed(lean_object* v_a_2534_, lean_object* v_x_2535_){
_start:
{
uint8_t v_res_2536_; lean_object* v_r_2537_; 
v_res_2536_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_2534_, v_x_2535_);
lean_dec(v_x_2535_);
lean_dec(v_a_2534_);
v_r_2537_ = lean_box(v_res_2536_);
return v_r_2537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10___redArg(lean_object* v_x_2538_, lean_object* v_x_2539_){
_start:
{
if (lean_obj_tag(v_x_2539_) == 0)
{
return v_x_2538_;
}
else
{
lean_object* v_key_2540_; lean_object* v_value_2541_; lean_object* v_tail_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2568_; 
v_key_2540_ = lean_ctor_get(v_x_2539_, 0);
v_value_2541_ = lean_ctor_get(v_x_2539_, 1);
v_tail_2542_ = lean_ctor_get(v_x_2539_, 2);
v_isSharedCheck_2568_ = !lean_is_exclusive(v_x_2539_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2544_ = v_x_2539_;
v_isShared_2545_ = v_isSharedCheck_2568_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_tail_2542_);
lean_inc(v_value_2541_);
lean_inc(v_key_2540_);
lean_dec(v_x_2539_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2568_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2546_; uint64_t v___y_2548_; 
v___x_2546_ = lean_array_get_size(v_x_2538_);
if (lean_obj_tag(v_key_2540_) == 0)
{
uint64_t v___x_2566_; 
v___x_2566_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
v___y_2548_ = v___x_2566_;
goto v___jp_2547_;
}
else
{
uint64_t v_hash_2567_; 
v_hash_2567_ = lean_ctor_get_uint64(v_key_2540_, sizeof(void*)*2);
v___y_2548_ = v_hash_2567_;
goto v___jp_2547_;
}
v___jp_2547_:
{
uint64_t v___x_2549_; uint64_t v___x_2550_; uint64_t v_fold_2551_; uint64_t v___x_2552_; uint64_t v___x_2553_; uint64_t v___x_2554_; size_t v___x_2555_; size_t v___x_2556_; size_t v___x_2557_; size_t v___x_2558_; size_t v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2562_; 
v___x_2549_ = 32ULL;
v___x_2550_ = lean_uint64_shift_right(v___y_2548_, v___x_2549_);
v_fold_2551_ = lean_uint64_xor(v___y_2548_, v___x_2550_);
v___x_2552_ = 16ULL;
v___x_2553_ = lean_uint64_shift_right(v_fold_2551_, v___x_2552_);
v___x_2554_ = lean_uint64_xor(v_fold_2551_, v___x_2553_);
v___x_2555_ = lean_uint64_to_usize(v___x_2554_);
v___x_2556_ = lean_usize_of_nat(v___x_2546_);
v___x_2557_ = ((size_t)1ULL);
v___x_2558_ = lean_usize_sub(v___x_2556_, v___x_2557_);
v___x_2559_ = lean_usize_land(v___x_2555_, v___x_2558_);
v___x_2560_ = lean_array_uget_borrowed(v_x_2538_, v___x_2559_);
lean_inc(v___x_2560_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 2, v___x_2560_);
v___x_2562_ = v___x_2544_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_key_2540_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_value_2541_);
lean_ctor_set(v_reuseFailAlloc_2565_, 2, v___x_2560_);
v___x_2562_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
lean_object* v___x_2563_; 
v___x_2563_ = lean_array_uset(v_x_2538_, v___x_2559_, v___x_2562_);
v_x_2538_ = v___x_2563_;
v_x_2539_ = v_tail_2542_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8___redArg(lean_object* v_i_2569_, lean_object* v_source_2570_, lean_object* v_target_2571_){
_start:
{
lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2572_ = lean_array_get_size(v_source_2570_);
v___x_2573_ = lean_nat_dec_lt(v_i_2569_, v___x_2572_);
if (v___x_2573_ == 0)
{
lean_dec_ref(v_source_2570_);
lean_dec(v_i_2569_);
return v_target_2571_;
}
else
{
lean_object* v_es_2574_; lean_object* v___x_2575_; lean_object* v_source_2576_; lean_object* v_target_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v_es_2574_ = lean_array_fget(v_source_2570_, v_i_2569_);
v___x_2575_ = lean_box(0);
v_source_2576_ = lean_array_fset(v_source_2570_, v_i_2569_, v___x_2575_);
v_target_2577_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10___redArg(v_target_2571_, v_es_2574_);
v___x_2578_ = lean_unsigned_to_nat(1u);
v___x_2579_ = lean_nat_add(v_i_2569_, v___x_2578_);
lean_dec(v_i_2569_);
v_i_2569_ = v___x_2579_;
v_source_2570_ = v_source_2576_;
v_target_2571_ = v_target_2577_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(lean_object* v_data_2581_){
_start:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v_nbuckets_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2582_ = lean_array_get_size(v_data_2581_);
v___x_2583_ = lean_unsigned_to_nat(2u);
v_nbuckets_2584_ = lean_nat_mul(v___x_2582_, v___x_2583_);
v___x_2585_ = lean_unsigned_to_nat(0u);
v___x_2586_ = lean_box(0);
v___x_2587_ = lean_mk_array(v_nbuckets_2584_, v___x_2586_);
v___x_2588_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8___redArg(v___x_2585_, v_data_2581_, v___x_2587_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0___redArg(lean_object* v_m_2589_, lean_object* v_a_2590_, lean_object* v_b_2591_){
_start:
{
lean_object* v_size_2592_; lean_object* v_buckets_2593_; lean_object* v___x_2594_; uint64_t v___y_2596_; 
v_size_2592_ = lean_ctor_get(v_m_2589_, 0);
v_buckets_2593_ = lean_ctor_get(v_m_2589_, 1);
v___x_2594_ = lean_array_get_size(v_buckets_2593_);
if (lean_obj_tag(v_a_2590_) == 0)
{
uint64_t v___x_2633_; 
v___x_2633_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
v___y_2596_ = v___x_2633_;
goto v___jp_2595_;
}
else
{
uint64_t v_hash_2634_; 
v_hash_2634_ = lean_ctor_get_uint64(v_a_2590_, sizeof(void*)*2);
v___y_2596_ = v_hash_2634_;
goto v___jp_2595_;
}
v___jp_2595_:
{
uint64_t v___x_2597_; uint64_t v___x_2598_; uint64_t v_fold_2599_; uint64_t v___x_2600_; uint64_t v___x_2601_; uint64_t v___x_2602_; size_t v___x_2603_; size_t v___x_2604_; size_t v___x_2605_; size_t v___x_2606_; size_t v___x_2607_; lean_object* v_bkt_2608_; uint8_t v___x_2609_; 
v___x_2597_ = 32ULL;
v___x_2598_ = lean_uint64_shift_right(v___y_2596_, v___x_2597_);
v_fold_2599_ = lean_uint64_xor(v___y_2596_, v___x_2598_);
v___x_2600_ = 16ULL;
v___x_2601_ = lean_uint64_shift_right(v_fold_2599_, v___x_2600_);
v___x_2602_ = lean_uint64_xor(v_fold_2599_, v___x_2601_);
v___x_2603_ = lean_uint64_to_usize(v___x_2602_);
v___x_2604_ = lean_usize_of_nat(v___x_2594_);
v___x_2605_ = ((size_t)1ULL);
v___x_2606_ = lean_usize_sub(v___x_2604_, v___x_2605_);
v___x_2607_ = lean_usize_land(v___x_2603_, v___x_2606_);
v_bkt_2608_ = lean_array_uget_borrowed(v_buckets_2593_, v___x_2607_);
v___x_2609_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_2590_, v_bkt_2608_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2630_; 
lean_inc_ref(v_buckets_2593_);
lean_inc(v_size_2592_);
v_isSharedCheck_2630_ = !lean_is_exclusive(v_m_2589_);
if (v_isSharedCheck_2630_ == 0)
{
lean_object* v_unused_2631_; lean_object* v_unused_2632_; 
v_unused_2631_ = lean_ctor_get(v_m_2589_, 1);
lean_dec(v_unused_2631_);
v_unused_2632_ = lean_ctor_get(v_m_2589_, 0);
lean_dec(v_unused_2632_);
v___x_2611_ = v_m_2589_;
v_isShared_2612_ = v_isSharedCheck_2630_;
goto v_resetjp_2610_;
}
else
{
lean_dec(v_m_2589_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2630_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2613_; lean_object* v_size_x27_2614_; lean_object* v___x_2615_; lean_object* v_buckets_x27_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2613_ = lean_unsigned_to_nat(1u);
v_size_x27_2614_ = lean_nat_add(v_size_2592_, v___x_2613_);
lean_dec(v_size_2592_);
lean_inc(v_bkt_2608_);
v___x_2615_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2615_, 0, v_a_2590_);
lean_ctor_set(v___x_2615_, 1, v_b_2591_);
lean_ctor_set(v___x_2615_, 2, v_bkt_2608_);
v_buckets_x27_2616_ = lean_array_uset(v_buckets_2593_, v___x_2607_, v___x_2615_);
v___x_2617_ = lean_unsigned_to_nat(4u);
v___x_2618_ = lean_nat_mul(v_size_x27_2614_, v___x_2617_);
v___x_2619_ = lean_unsigned_to_nat(3u);
v___x_2620_ = lean_nat_div(v___x_2618_, v___x_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_array_get_size(v_buckets_x27_2616_);
v___x_2622_ = lean_nat_dec_le(v___x_2620_, v___x_2621_);
lean_dec(v___x_2620_);
if (v___x_2622_ == 0)
{
lean_object* v_val_2623_; lean_object* v___x_2625_; 
v_val_2623_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(v_buckets_x27_2616_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 1, v_val_2623_);
lean_ctor_set(v___x_2611_, 0, v_size_x27_2614_);
v___x_2625_ = v___x_2611_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_size_x27_2614_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v_val_2623_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
else
{
lean_object* v___x_2628_; 
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 1, v_buckets_x27_2616_);
lean_ctor_set(v___x_2611_, 0, v_size_x27_2614_);
v___x_2628_ = v___x_2611_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_size_x27_2614_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v_buckets_x27_2616_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
else
{
lean_dec(v_b_2591_);
lean_dec(v_a_2590_);
return v_m_2589_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1(lean_object* v_as_2635_, size_t v_sz_2636_, size_t v_i_2637_, lean_object* v_b_2638_){
_start:
{
uint8_t v___x_2639_; 
v___x_2639_ = lean_usize_dec_lt(v_i_2637_, v_sz_2636_);
if (v___x_2639_ == 0)
{
return v_b_2638_;
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2641_; lean_object* v_r_2642_; size_t v___x_2643_; size_t v___x_2644_; 
v_a_2640_ = lean_array_uget_borrowed(v_as_2635_, v_i_2637_);
v___x_2641_ = lean_box(0);
lean_inc(v_a_2640_);
v_r_2642_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0___redArg(v_b_2638_, v_a_2640_, v___x_2641_);
v___x_2643_ = ((size_t)1ULL);
v___x_2644_ = lean_usize_add(v_i_2637_, v___x_2643_);
v_i_2637_ = v___x_2644_;
v_b_2638_ = v_r_2642_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1___boxed(lean_object* v_as_2646_, lean_object* v_sz_2647_, lean_object* v_i_2648_, lean_object* v_b_2649_){
_start:
{
size_t v_sz_boxed_2650_; size_t v_i_boxed_2651_; lean_object* v_res_2652_; 
v_sz_boxed_2650_ = lean_unbox_usize(v_sz_2647_);
lean_dec(v_sz_2647_);
v_i_boxed_2651_ = lean_unbox_usize(v_i_2648_);
lean_dec(v_i_2648_);
v_res_2652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1(v_as_2646_, v_sz_boxed_2650_, v_i_boxed_2651_, v_b_2649_);
lean_dec_ref(v_as_2646_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0(lean_object* v_m_2653_, lean_object* v_l_2654_){
_start:
{
size_t v_sz_2655_; size_t v___x_2656_; lean_object* v___x_2657_; 
v_sz_2655_ = lean_array_size(v_l_2654_);
v___x_2656_ = ((size_t)0ULL);
v___x_2657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__1(v_l_2654_, v_sz_2655_, v___x_2656_, v_m_2653_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0___boxed(lean_object* v_m_2658_, lean_object* v_l_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0(v_m_2658_, v_l_2659_);
lean_dec_ref(v_l_2659_);
return v_res_2660_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(lean_object* v_m_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v_buckets_2663_; lean_object* v___x_2664_; uint64_t v___y_2666_; 
v_buckets_2663_ = lean_ctor_get(v_m_2661_, 1);
v___x_2664_ = lean_array_get_size(v_buckets_2663_);
if (lean_obj_tag(v_a_2662_) == 0)
{
uint64_t v___x_2680_; 
v___x_2680_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
v___y_2666_ = v___x_2680_;
goto v___jp_2665_;
}
else
{
uint64_t v_hash_2681_; 
v_hash_2681_ = lean_ctor_get_uint64(v_a_2662_, sizeof(void*)*2);
v___y_2666_ = v_hash_2681_;
goto v___jp_2665_;
}
v___jp_2665_:
{
uint64_t v___x_2667_; uint64_t v___x_2668_; uint64_t v_fold_2669_; uint64_t v___x_2670_; uint64_t v___x_2671_; uint64_t v___x_2672_; size_t v___x_2673_; size_t v___x_2674_; size_t v___x_2675_; size_t v___x_2676_; size_t v___x_2677_; lean_object* v___x_2678_; uint8_t v___x_2679_; 
v___x_2667_ = 32ULL;
v___x_2668_ = lean_uint64_shift_right(v___y_2666_, v___x_2667_);
v_fold_2669_ = lean_uint64_xor(v___y_2666_, v___x_2668_);
v___x_2670_ = 16ULL;
v___x_2671_ = lean_uint64_shift_right(v_fold_2669_, v___x_2670_);
v___x_2672_ = lean_uint64_xor(v_fold_2669_, v___x_2671_);
v___x_2673_ = lean_uint64_to_usize(v___x_2672_);
v___x_2674_ = lean_usize_of_nat(v___x_2664_);
v___x_2675_ = ((size_t)1ULL);
v___x_2676_ = lean_usize_sub(v___x_2674_, v___x_2675_);
v___x_2677_ = lean_usize_land(v___x_2673_, v___x_2676_);
v___x_2678_ = lean_array_uget_borrowed(v_buckets_2663_, v___x_2677_);
v___x_2679_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_2662_, v___x_2678_);
return v___x_2679_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg___boxed(lean_object* v_m_2682_, lean_object* v_a_2683_){
_start:
{
uint8_t v_res_2684_; lean_object* v_r_2685_; 
v_res_2684_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(v_m_2682_, v_a_2683_);
lean_dec(v_a_2683_);
lean_dec_ref(v_m_2682_);
v_r_2685_ = lean_box(v_res_2684_);
return v_r_2685_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(lean_object* v_a_2686_, lean_object* v_b_2687_, lean_object* v_x_2688_){
_start:
{
if (lean_obj_tag(v_x_2688_) == 0)
{
lean_dec(v_b_2687_);
lean_dec(v_a_2686_);
return v_x_2688_;
}
else
{
lean_object* v_key_2689_; lean_object* v_value_2690_; lean_object* v_tail_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2703_; 
v_key_2689_ = lean_ctor_get(v_x_2688_, 0);
v_value_2690_ = lean_ctor_get(v_x_2688_, 1);
v_tail_2691_ = lean_ctor_get(v_x_2688_, 2);
v_isSharedCheck_2703_ = !lean_is_exclusive(v_x_2688_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2693_ = v_x_2688_;
v_isShared_2694_ = v_isSharedCheck_2703_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_tail_2691_);
lean_inc(v_value_2690_);
lean_inc(v_key_2689_);
lean_dec(v_x_2688_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2703_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
uint8_t v___x_2695_; 
v___x_2695_ = lean_name_eq(v_key_2689_, v_a_2686_);
if (v___x_2695_ == 0)
{
lean_object* v___x_2696_; lean_object* v___x_2698_; 
v___x_2696_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(v_a_2686_, v_b_2687_, v_tail_2691_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 2, v___x_2696_);
v___x_2698_ = v___x_2693_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_key_2689_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_value_2690_);
lean_ctor_set(v_reuseFailAlloc_2699_, 2, v___x_2696_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
else
{
lean_object* v___x_2701_; 
lean_dec(v_value_2690_);
lean_dec(v_key_2689_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set(v___x_2693_, 1, v_b_2687_);
lean_ctor_set(v___x_2693_, 0, v_a_2686_);
v___x_2701_ = v___x_2693_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2686_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v_b_2687_);
lean_ctor_set(v_reuseFailAlloc_2702_, 2, v_tail_2691_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3___redArg(lean_object* v_m_2704_, lean_object* v_a_2705_, lean_object* v_b_2706_){
_start:
{
lean_object* v_size_2707_; lean_object* v_buckets_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2754_; 
v_size_2707_ = lean_ctor_get(v_m_2704_, 0);
v_buckets_2708_ = lean_ctor_get(v_m_2704_, 1);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_m_2704_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2710_ = v_m_2704_;
v_isShared_2711_ = v_isSharedCheck_2754_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_buckets_2708_);
lean_inc(v_size_2707_);
lean_dec(v_m_2704_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2754_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2712_; uint64_t v___y_2714_; 
v___x_2712_ = lean_array_get_size(v_buckets_2708_);
if (lean_obj_tag(v_a_2705_) == 0)
{
uint64_t v___x_2752_; 
v___x_2752_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_replayFn_spec__0___redArg___closed__0);
v___y_2714_ = v___x_2752_;
goto v___jp_2713_;
}
else
{
uint64_t v_hash_2753_; 
v_hash_2753_ = lean_ctor_get_uint64(v_a_2705_, sizeof(void*)*2);
v___y_2714_ = v_hash_2753_;
goto v___jp_2713_;
}
v___jp_2713_:
{
uint64_t v___x_2715_; uint64_t v___x_2716_; uint64_t v_fold_2717_; uint64_t v___x_2718_; uint64_t v___x_2719_; uint64_t v___x_2720_; size_t v___x_2721_; size_t v___x_2722_; size_t v___x_2723_; size_t v___x_2724_; size_t v___x_2725_; lean_object* v_bkt_2726_; uint8_t v___x_2727_; 
v___x_2715_ = 32ULL;
v___x_2716_ = lean_uint64_shift_right(v___y_2714_, v___x_2715_);
v_fold_2717_ = lean_uint64_xor(v___y_2714_, v___x_2716_);
v___x_2718_ = 16ULL;
v___x_2719_ = lean_uint64_shift_right(v_fold_2717_, v___x_2718_);
v___x_2720_ = lean_uint64_xor(v_fold_2717_, v___x_2719_);
v___x_2721_ = lean_uint64_to_usize(v___x_2720_);
v___x_2722_ = lean_usize_of_nat(v___x_2712_);
v___x_2723_ = ((size_t)1ULL);
v___x_2724_ = lean_usize_sub(v___x_2722_, v___x_2723_);
v___x_2725_ = lean_usize_land(v___x_2721_, v___x_2724_);
v_bkt_2726_ = lean_array_uget_borrowed(v_buckets_2708_, v___x_2725_);
v___x_2727_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_2705_, v_bkt_2726_);
if (v___x_2727_ == 0)
{
lean_object* v___x_2728_; lean_object* v_size_x27_2729_; lean_object* v___x_2730_; lean_object* v_buckets_x27_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; uint8_t v___x_2737_; 
v___x_2728_ = lean_unsigned_to_nat(1u);
v_size_x27_2729_ = lean_nat_add(v_size_2707_, v___x_2728_);
lean_dec(v_size_2707_);
lean_inc(v_bkt_2726_);
v___x_2730_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2730_, 0, v_a_2705_);
lean_ctor_set(v___x_2730_, 1, v_b_2706_);
lean_ctor_set(v___x_2730_, 2, v_bkt_2726_);
v_buckets_x27_2731_ = lean_array_uset(v_buckets_2708_, v___x_2725_, v___x_2730_);
v___x_2732_ = lean_unsigned_to_nat(4u);
v___x_2733_ = lean_nat_mul(v_size_x27_2729_, v___x_2732_);
v___x_2734_ = lean_unsigned_to_nat(3u);
v___x_2735_ = lean_nat_div(v___x_2733_, v___x_2734_);
lean_dec(v___x_2733_);
v___x_2736_ = lean_array_get_size(v_buckets_x27_2731_);
v___x_2737_ = lean_nat_dec_le(v___x_2735_, v___x_2736_);
lean_dec(v___x_2735_);
if (v___x_2737_ == 0)
{
lean_object* v_val_2738_; lean_object* v___x_2740_; 
v_val_2738_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(v_buckets_x27_2731_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 1, v_val_2738_);
lean_ctor_set(v___x_2710_, 0, v_size_x27_2729_);
v___x_2740_ = v___x_2710_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_size_x27_2729_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v_val_2738_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
else
{
lean_object* v___x_2743_; 
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 1, v_buckets_x27_2731_);
lean_ctor_set(v___x_2710_, 0, v_size_x27_2729_);
v___x_2743_ = v___x_2710_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_size_x27_2729_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_buckets_x27_2731_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
else
{
lean_object* v___x_2745_; lean_object* v_buckets_x27_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2750_; 
lean_inc(v_bkt_2726_);
v___x_2745_ = lean_box(0);
v_buckets_x27_2746_ = lean_array_uset(v_buckets_2708_, v___x_2725_, v___x_2745_);
v___x_2747_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(v_a_2705_, v_b_2706_, v_bkt_2726_);
v___x_2748_ = lean_array_uset(v_buckets_x27_2746_, v___x_2725_, v___x_2747_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 1, v___x_2748_);
v___x_2750_ = v___x_2710_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_size_2707_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v___x_2748_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2758_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__2));
v___x_2759_ = lean_unsigned_to_nat(4u);
v___x_2760_ = lean_unsigned_to_nat(240u);
v___x_2761_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__1));
v___x_2762_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__0));
v___x_2763_ = l_mkPanicMessageWithDecl(v___x_2762_, v___x_2761_, v___x_2760_, v___x_2759_, v___x_2758_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(lean_object* v___x_2764_, lean_object* v_as_x27_2765_, lean_object* v_b_2766_){
_start:
{
if (lean_obj_tag(v_as_x27_2765_) == 0)
{
return v_b_2766_;
}
else
{
lean_object* v_head_2767_; lean_object* v_tail_2768_; lean_object* v_fst_2769_; lean_object* v_snd_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2791_; 
v_head_2767_ = lean_ctor_get(v_as_x27_2765_, 0);
lean_inc(v_head_2767_);
v_tail_2768_ = lean_ctor_get(v_as_x27_2765_, 1);
lean_inc(v_tail_2768_);
lean_dec_ref(v_as_x27_2765_);
v_fst_2769_ = lean_ctor_get(v_b_2766_, 0);
v_snd_2770_ = lean_ctor_get(v_b_2766_, 1);
v_isSharedCheck_2791_ = !lean_is_exclusive(v_b_2766_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2772_ = v_b_2766_;
v_isShared_2773_ = v_isSharedCheck_2791_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_snd_2770_);
lean_inc(v_fst_2769_);
lean_dec(v_b_2766_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2791_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v_map_2775_; uint8_t v___x_2789_; 
v___x_2789_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(v___x_2764_, v_head_2767_);
if (v___x_2789_ == 0)
{
lean_dec(v_head_2767_);
v_map_2775_ = v_fst_2769_;
goto v___jp_2774_;
}
else
{
lean_object* v___x_2790_; 
lean_inc(v_snd_2770_);
v___x_2790_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3___redArg(v_fst_2769_, v_head_2767_, v_snd_2770_);
v_map_2775_ = v___x_2790_;
goto v___jp_2774_;
}
v___jp_2774_:
{
lean_object* v___x_2776_; uint8_t v___x_2777_; 
v___x_2776_ = lean_unsigned_to_nat(0u);
v___x_2777_ = lean_nat_dec_eq(v_snd_2770_, v___x_2776_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2781_; 
v___x_2778_ = lean_unsigned_to_nat(1u);
v___x_2779_ = lean_nat_sub(v_snd_2770_, v___x_2778_);
lean_dec(v_snd_2770_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 1, v___x_2779_);
lean_ctor_set(v___x_2772_, 0, v_map_2775_);
v___x_2781_ = v___x_2772_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_map_2775_);
lean_ctor_set(v_reuseFailAlloc_2783_, 1, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
v_as_x27_2765_ = v_tail_2768_;
v_b_2766_ = v___x_2781_;
goto _start;
}
}
else
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
lean_dec_ref(v_map_2775_);
lean_del_object(v___x_2772_);
lean_dec(v_snd_2770_);
v___x_2784_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__3);
v___x_2785_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__1(v___x_2784_);
if (lean_obj_tag(v___x_2785_) == 0)
{
lean_object* v_a_2786_; 
lean_dec(v_tail_2768_);
v_a_2786_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2786_);
lean_dec_ref(v___x_2785_);
return v_a_2786_;
}
else
{
lean_object* v_a_2787_; 
v_a_2787_ = lean_ctor_get(v___x_2785_, 0);
lean_inc(v_a_2787_);
lean_dec_ref(v___x_2785_);
v_as_x27_2765_ = v_tail_2768_;
v_b_2766_ = v_a_2787_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___boxed(lean_object* v___x_2792_, lean_object* v_as_x27_2793_, lean_object* v_b_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(v___x_2792_, v_as_x27_2793_, v_b_2794_);
lean_dec_ref(v___x_2792_);
return v_res_2795_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0(void){
_start:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2796_ = lean_box(0);
v___x_2797_ = lean_unsigned_to_nat(16u);
v___x_2798_ = lean_mk_array(v___x_2797_, v___x_2796_);
return v___x_2798_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1(void){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2799_ = lean_obj_once(&l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0, &l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0_once, _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__0);
v___x_2800_ = lean_unsigned_to_nat(0u);
v___x_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
lean_ctor_set(v___x_2801_, 1, v___x_2799_);
return v___x_2801_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3(void){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2803_ = ((lean_object*)(l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__2));
v___x_2804_ = lean_unsigned_to_nat(2u);
v___x_2805_ = lean_unsigned_to_nat(242u);
v___x_2806_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__1));
v___x_2807_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg___closed__0));
v___x_2808_ = l_mkPanicMessageWithDecl(v___x_2807_, v___x_2806_, v___x_2805_, v___x_2804_, v___x_2803_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureDeclIndices(lean_object* v_env_2809_, lean_object* v_targets_2810_){
_start:
{
lean_object* v___x_2811_; lean_object* v_asyncMode_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v_fst_2816_; lean_object* v_snd_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2846_; 
v___x_2811_ = l_Lean_Compiler_LCNF_declOrderExt;
v_asyncMode_2812_ = lean_ctor_get(v___x_2811_, 2);
lean_inc(v_asyncMode_2812_);
v___x_2813_ = ((lean_object*)(l_Lean_Compiler_LCNF_isDeclTransparent___closed__0));
v___x_2814_ = lean_box(0);
v___x_2815_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2813_, v___x_2811_, v_env_2809_, v_asyncMode_2812_, v___x_2814_);
lean_dec(v_asyncMode_2812_);
v_fst_2816_ = lean_ctor_get(v___x_2815_, 0);
v_snd_2817_ = lean_ctor_get(v___x_2815_, 1);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2819_ = v___x_2815_;
v_isShared_2820_ = v_isSharedCheck_2846_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_snd_2817_);
lean_inc(v_fst_2816_);
lean_dec(v___x_2815_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2846_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___y_2822_; 
if (lean_obj_tag(v_snd_2817_) == 0)
{
lean_object* v_size_2844_; 
v_size_2844_ = lean_ctor_get(v_snd_2817_, 0);
lean_inc(v_size_2844_);
lean_dec_ref(v_snd_2817_);
v___y_2822_ = v_size_2844_;
goto v___jp_2821_;
}
else
{
lean_object* v___x_2845_; 
v___x_2845_ = lean_unsigned_to_nat(0u);
v___y_2822_ = v___x_2845_;
goto v___jp_2821_;
}
v___jp_2821_:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v_map_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2835_; 
v___x_2823_ = lean_unsigned_to_nat(0u);
v___x_2824_ = lean_unsigned_to_nat(4u);
v___x_2825_ = lean_nat_mul(v___y_2822_, v___x_2824_);
v___x_2826_ = lean_unsigned_to_nat(3u);
v___x_2827_ = lean_nat_div(v___x_2825_, v___x_2826_);
lean_dec(v___x_2825_);
v___x_2828_ = l_Nat_nextPowerOfTwo(v___x_2827_);
lean_dec(v___x_2827_);
v___x_2829_ = lean_box(0);
v___x_2830_ = lean_mk_array(v___x_2828_, v___x_2829_);
v_map_2831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_map_2831_, 0, v___x_2823_);
lean_ctor_set(v_map_2831_, 1, v___x_2830_);
v___x_2832_ = lean_obj_once(&l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1, &l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1_once, _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__1);
v___x_2833_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0(v___x_2832_, v_targets_2810_);
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 1, v___y_2822_);
lean_ctor_set(v___x_2819_, 0, v_map_2831_);
v___x_2835_ = v___x_2819_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_map_2831_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v___y_2822_);
v___x_2835_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
lean_object* v___x_2836_; lean_object* v_fst_2837_; lean_object* v_size_2838_; lean_object* v___x_2839_; uint8_t v___x_2840_; 
v___x_2836_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(v___x_2833_, v_fst_2816_, v___x_2835_);
lean_dec_ref(v___x_2833_);
v_fst_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_fst_2837_);
lean_dec_ref(v___x_2836_);
v_size_2838_ = lean_ctor_get(v_fst_2837_, 0);
v___x_2839_ = lean_array_get_size(v_targets_2810_);
v___x_2840_ = lean_nat_dec_eq(v_size_2838_, v___x_2839_);
if (v___x_2840_ == 0)
{
lean_object* v___x_2841_; lean_object* v___x_2842_; 
lean_dec(v_fst_2837_);
v___x_2841_ = lean_obj_once(&l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3, &l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3_once, _init_l_Lean_Compiler_LCNF_getImpureDeclIndices___closed__3);
v___x_2842_ = l_panic___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__5(v___x_2841_);
return v___x_2842_;
}
else
{
return v_fst_2837_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getImpureDeclIndices___boxed(lean_object* v_env_2847_, lean_object* v_targets_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Lean_Compiler_LCNF_getImpureDeclIndices(v_env_2847_, v_targets_2848_);
lean_dec_ref(v_targets_2848_);
return v_res_2849_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2(lean_object* v_00_u03b2_2850_, lean_object* v_m_2851_, lean_object* v_a_2852_){
_start:
{
uint8_t v___x_2853_; 
v___x_2853_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___redArg(v_m_2851_, v_a_2852_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2___boxed(lean_object* v_00_u03b2_2854_, lean_object* v_m_2855_, lean_object* v_a_2856_){
_start:
{
uint8_t v_res_2857_; lean_object* v_r_2858_; 
v_res_2857_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2(v_00_u03b2_2854_, v_m_2855_, v_a_2856_);
lean_dec(v_a_2856_);
lean_dec_ref(v_m_2855_);
v_r_2858_ = lean_box(v_res_2857_);
return v_r_2858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3(lean_object* v_00_u03b2_2859_, lean_object* v_m_2860_, lean_object* v_a_2861_, lean_object* v_b_2862_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3___redArg(v_m_2860_, v_a_2861_, v_b_2862_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4(lean_object* v___x_2864_, lean_object* v_as_2865_, lean_object* v_as_x27_2866_, lean_object* v_b_2867_, lean_object* v_a_2868_){
_start:
{
lean_object* v___x_2869_; 
v___x_2869_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___redArg(v___x_2864_, v_as_x27_2866_, v_b_2867_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4___boxed(lean_object* v___x_2870_, lean_object* v_as_2871_, lean_object* v_as_x27_2872_, lean_object* v_b_2873_, lean_object* v_a_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__4(v___x_2870_, v_as_2871_, v_as_x27_2872_, v_b_2873_, v_a_2874_);
lean_dec(v_as_2871_);
lean_dec_ref(v___x_2870_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0(lean_object* v_00_u03b2_2876_, lean_object* v_m_2877_, lean_object* v_a_2878_, lean_object* v_b_2879_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__0_spec__0___redArg(v_m_2877_, v_a_2878_, v_b_2879_);
return v___x_2880_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4(lean_object* v_00_u03b2_2881_, lean_object* v_a_2882_, lean_object* v_x_2883_){
_start:
{
uint8_t v___x_2884_; 
v___x_2884_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___redArg(v_a_2882_, v_x_2883_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4___boxed(lean_object* v_00_u03b2_2885_, lean_object* v_a_2886_, lean_object* v_x_2887_){
_start:
{
uint8_t v_res_2888_; lean_object* v_r_2889_; 
v_res_2888_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__2_spec__4(v_00_u03b2_2885_, v_a_2886_, v_x_2887_);
lean_dec(v_x_2887_);
lean_dec(v_a_2886_);
v_r_2889_ = lean_box(v_res_2888_);
return v_r_2889_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6(lean_object* v_00_u03b2_2890_, lean_object* v_data_2891_){
_start:
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6___redArg(v_data_2891_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7(lean_object* v_00_u03b2_2893_, lean_object* v_a_2894_, lean_object* v_b_2895_, lean_object* v_x_2896_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__7___redArg(v_a_2894_, v_b_2895_, v_x_2896_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_2898_, lean_object* v_i_2899_, lean_object* v_source_2900_, lean_object* v_target_2901_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8___redArg(v_i_2899_, v_source_2900_, v_target_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10(lean_object* v_00_u03b2_2903_, lean_object* v_x_2904_, lean_object* v_x_2905_){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_getImpureDeclIndices_spec__3_spec__6_spec__8_spec__10___redArg(v_x_2904_, v_x_2905_);
return v___x_2906_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3496178540____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_baseTransparentDeclsExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_baseTransparentDeclsExt);
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1977385844____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_monoTransparentDeclsExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_monoTransparentDeclsExt);
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_975450157____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_impureTransparentDeclsExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_LCNF_PhaseExt_0__Lean_Compiler_LCNF_impureTransparentDeclsExt);
lean_dec_ref(res);
res = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_1453085006____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_baseExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_baseExt);
lean_dec_ref(res);
res = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_3223139564____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_monoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_monoExt);
lean_dec_ref(res);
res = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_882283628____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_impureExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_impureExt);
lean_dec_ref(res);
res = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_346366741____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_impureSigExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_impureSigExt);
lean_dec_ref(res);
res = l_Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PhaseExt_2540780834____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_declOrderExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_declOrderExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Compiler_LCNF_mkDeclExt___auto__1 = _init_l_Lean_Compiler_LCNF_mkDeclExt___auto__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkDeclExt___auto__1);
l_Lean_Compiler_LCNF_mkSigDeclExt___auto__1 = _init_l_Lean_Compiler_LCNF_mkSigDeclExt___auto__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkSigDeclExt___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_PublicDeclsExt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
}
#ifdef __cplusplus
}
#endif
