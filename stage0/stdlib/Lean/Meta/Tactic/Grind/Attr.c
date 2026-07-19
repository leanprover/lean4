// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Attr
// Imports: public import Lean.Meta.Tactic.Grind.Injective public import Lean.Meta.Tactic.Grind.Cases public import Lean.Meta.Tactic.Grind.ExtAttr public import Lean.Meta.Tactic.Simp.Attr public import Lean.Meta.Tactic.Grind.Homo import Lean.Meta.Sym.Simp.Attr import Lean.ExtraModUses
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
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_Meta_Grind_Theorems_contains___redArg(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ExtTheorems_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkExtension(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSimpExt(lean_object*);
lean_object* l_Lean_Meta_addDeclToUnfold(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_homoExt;
lean_object* l_Lean_Meta_Sym_Simp_addSymSimpDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addEMatchAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_validateCasesAttr(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_validateExtAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addSymbolPriorityAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addInjectiveAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_CasesTypes_isSplit(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "normExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 117, 24, 11, 244, 218, 170, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindMod"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 252, 83, 80, 136, 168, 19, 119)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "unexpected `grind` theorem kind: `"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__5;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__7;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindEq"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value),LEAN_SCALAR_PTR_LITERAL(179, 34, 219, 24, 240, 38, 65, 204)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindDef"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value),LEAN_SCALAR_PTR_LITERAL(66, 218, 12, 28, 39, 29, 4, 77)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindFwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value),LEAN_SCALAR_PTR_LITERAL(121, 161, 177, 116, 112, 162, 92, 47)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindBwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value),LEAN_SCALAR_PTR_LITERAL(114, 163, 57, 243, 160, 41, 114, 23)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindEqRhs"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value),LEAN_SCALAR_PTR_LITERAL(222, 187, 148, 221, 105, 213, 199, 68)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindEqBoth"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value),LEAN_SCALAR_PTR_LITERAL(79, 230, 133, 190, 186, 228, 109, 128)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindEqBwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value),LEAN_SCALAR_PTR_LITERAL(250, 57, 23, 180, 238, 116, 90, 53)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindLR"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value),LEAN_SCALAR_PTR_LITERAL(152, 111, 188, 78, 132, 212, 97, 164)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindRL"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__24 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value),LEAN_SCALAR_PTR_LITERAL(84, 112, 237, 169, 105, 148, 42, 205)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindUsr"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value),LEAN_SCALAR_PTR_LITERAL(204, 58, 160, 148, 192, 167, 114, 18)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindGen"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value),LEAN_SCALAR_PTR_LITERAL(186, 203, 120, 147, 97, 215, 208, 134)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__29 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindCases"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__30 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value),LEAN_SCALAR_PTR_LITERAL(85, 142, 28, 230, 49, 50, 229, 162)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__31 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "grindCasesEager"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__32 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value),LEAN_SCALAR_PTR_LITERAL(75, 210, 92, 40, 190, 183, 142, 70)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__33 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindIntro"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value),LEAN_SCALAR_PTR_LITERAL(142, 126, 114, 89, 237, 253, 56, 138)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__35 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindExt"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__36 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value),LEAN_SCALAR_PTR_LITERAL(147, 193, 153, 166, 243, 149, 163, 253)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__37 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindInj"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__38 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value),LEAN_SCALAR_PTR_LITERAL(223, 225, 41, 9, 21, 5, 145, 193)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__39 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindFunCC"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__40 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value),LEAN_SCALAR_PTR_LITERAL(217, 20, 186, 134, 249, 79, 78, 43)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__41 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindNorm"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__42 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value),LEAN_SCALAR_PTR_LITERAL(166, 126, 146, 239, 104, 253, 29, 148)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__43 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindUnfold"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__44 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value),LEAN_SCALAR_PTR_LITERAL(214, 181, 37, 92, 122, 232, 164, 219)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__45 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindHomo"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__46 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value),LEAN_SCALAR_PTR_LITERAL(88, 142, 231, 82, 214, 226, 8, 218)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__47 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSym"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__48 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value),LEAN_SCALAR_PTR_LITERAL(104, 204, 11, 169, 55, 109, 254, 23)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__49 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "priority expected"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__50 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__51;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__52 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpPost"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__53 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__53_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__53_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__54 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpPre"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__55 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__55_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__55_value),LEAN_SCALAR_PTR_LITERAL(197, 59, 48, 6, 36, 81, 149, 152)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__56 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__57 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__57_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__58 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__59 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__59_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__60 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__60_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__61 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__61_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__62 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__62_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__62_value)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__63 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__63_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "the modifier `usr` is only relevant in parameters for `grind only`"};
static const lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 115, .m_capacity = 115, .m_length = 114, .m_data = "\?]` is a helper attribute for displaying inferred patterns, if you want to remove the attribute, consider using `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "]` instead"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 8}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "cannot mark declaration to be unfolded by `grind`"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grind homo"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "invalid `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " intro]`, `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "` is not an inductive predicate"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "symbol priorities must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "normalizer must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "declaration to unfold must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "homomorphism rules must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "When applied to an equational theorem, `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " =]`, `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " =_]`, or `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = " _=_]`will mark the theorem for use in heuristic instantiations by the `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 136, .m_capacity = 136, .m_length = 135, .m_data = "` tactic,\n      using respectively the left-hand side, the right-hand side, or both sides of the theorem.When applied to a function, `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 112, .m_capacity = 112, .m_length = 111, .m_data = " =]` automatically annotates the equational theorems associated with that function.When applied to a theorem `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 183, .m_capacity = 183, .m_length = 180, .m_data = " ←]` will instantiate the theorem whenever it encounters the conclusion of the theorem\n      (that is, it will use the theorem for backwards reasoning).When applied to a theorem `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 190, .m_capacity = 190, .m_length = 187, .m_data = " →]` will instantiate the theorem whenever it encounters sufficiently many of the propositional hypotheses\n      (that is, it will use the theorem for forwards reasoning).The attribute `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "]` by itself will effectively try `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 68, .m_data = " ←]` (if the conclusion is sufficient for instantiation) and then `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 165, .m_capacity = 165, .m_length = 162, .m_data = " →]`.The `grind` tactic utilizes annotated theorems to add instances of matching patterns into the local context during proof search.For example, if a theorem `@["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 179, .m_capacity = 179, .m_length = 178, .m_data = " =] theorem foo_idempotent : foo (foo x) = foo x` is annotated,`grind` will add an instance of this theorem to the local context whenever it encounters the pattern `foo (foo x)`."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "The `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "]` attribute is used to annotate declarations."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "\?]` attribute is identical to the `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "]` attribute, but displays inferred pattern information."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 90, .m_capacity = 90, .m_length = 89, .m_data = "!]` attribute is used to annotate declarations, but selecting minimal indexable subterms."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "!\?]` attribute is identical to the `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "!]` attribute, but displays inferred pattern information."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "!"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!\?"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_extensionMapRef;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___auto__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value),LEAN_SCALAR_PTR_LITERAL(160, 1, 171, 211, 177, 132, 129, 49)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_grindExt;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 161, 226, 116, 111, 153, 146, 212)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "liaExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(148, 224, 62, 90, 13, 174, 224, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liaExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_));
v___x_12_ = l_Lean_Meta_mkSimpExt(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2____boxed(lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx(lean_object* v_x_15_){
_start:
{
switch(lean_obj_tag(v_x_15_))
{
case 0:
{
lean_object* v___x_16_; 
v___x_16_ = lean_unsigned_to_nat(0u);
return v___x_16_;
}
case 1:
{
lean_object* v___x_17_; 
v___x_17_ = lean_unsigned_to_nat(1u);
return v___x_17_;
}
case 2:
{
lean_object* v___x_18_; 
v___x_18_ = lean_unsigned_to_nat(2u);
return v___x_18_;
}
case 3:
{
lean_object* v___x_19_; 
v___x_19_ = lean_unsigned_to_nat(3u);
return v___x_19_;
}
case 4:
{
lean_object* v___x_20_; 
v___x_20_ = lean_unsigned_to_nat(4u);
return v___x_20_;
}
case 5:
{
lean_object* v___x_21_; 
v___x_21_ = lean_unsigned_to_nat(5u);
return v___x_21_;
}
case 6:
{
lean_object* v___x_22_; 
v___x_22_ = lean_unsigned_to_nat(6u);
return v___x_22_;
}
case 7:
{
lean_object* v___x_23_; 
v___x_23_ = lean_unsigned_to_nat(7u);
return v___x_23_;
}
case 8:
{
lean_object* v___x_24_; 
v___x_24_ = lean_unsigned_to_nat(8u);
return v___x_24_;
}
case 9:
{
lean_object* v___x_25_; 
v___x_25_ = lean_unsigned_to_nat(9u);
return v___x_25_;
}
default: 
{
lean_object* v___x_26_; 
v___x_26_ = lean_unsigned_to_nat(10u);
return v___x_26_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___boxed(lean_object* v_x_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Meta_Grind_AttrKind_ctorIdx(v_x_27_);
lean_dec(v_x_27_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(lean_object* v_t_29_, lean_object* v_k_30_){
_start:
{
switch(lean_obj_tag(v_t_29_))
{
case 0:
{
lean_object* v_k_31_; lean_object* v___x_32_; 
v_k_31_ = lean_ctor_get(v_t_29_, 0);
lean_inc(v_k_31_);
lean_dec_ref_known(v_t_29_, 1);
v___x_32_ = lean_apply_1(v_k_30_, v_k_31_);
return v___x_32_;
}
case 1:
{
uint8_t v_eager_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v_eager_33_ = lean_ctor_get_uint8(v_t_29_, 0);
lean_dec_ref_known(v_t_29_, 0);
v___x_34_ = lean_box(v_eager_33_);
v___x_35_ = lean_apply_1(v_k_30_, v___x_34_);
return v___x_35_;
}
case 5:
{
lean_object* v_prio_36_; lean_object* v___x_37_; 
v_prio_36_ = lean_ctor_get(v_t_29_, 0);
lean_inc(v_prio_36_);
lean_dec_ref_known(v_t_29_, 1);
v___x_37_ = lean_apply_1(v_k_30_, v_prio_36_);
return v___x_37_;
}
case 8:
{
uint8_t v_post_38_; uint8_t v_inv_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v_post_38_ = lean_ctor_get_uint8(v_t_29_, 0);
v_inv_39_ = lean_ctor_get_uint8(v_t_29_, 1);
lean_dec_ref_known(v_t_29_, 0);
v___x_40_ = lean_box(v_post_38_);
v___x_41_ = lean_box(v_inv_39_);
v___x_42_ = lean_apply_2(v_k_30_, v___x_40_, v___x_41_);
return v___x_42_;
}
default: 
{
lean_dec(v_t_29_);
return v_k_30_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim(lean_object* v_motive_43_, lean_object* v_ctorIdx_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_k_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_45_, v_k_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___boxed(lean_object* v_motive_49_, lean_object* v_ctorIdx_50_, lean_object* v_t_51_, lean_object* v_h_52_, lean_object* v_k_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Meta_Grind_AttrKind_ctorElim(v_motive_49_, v_ctorIdx_50_, v_t_51_, v_h_52_, v_k_53_);
lean_dec(v_ctorIdx_50_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim___redArg(lean_object* v_t_55_, lean_object* v_ematch_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_55_, v_ematch_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim(lean_object* v_motive_58_, lean_object* v_t_59_, lean_object* v_h_60_, lean_object* v_ematch_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_59_, v_ematch_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim___redArg(lean_object* v_t_63_, lean_object* v_cases_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_63_, v_cases_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim(lean_object* v_motive_66_, lean_object* v_t_67_, lean_object* v_h_68_, lean_object* v_cases_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_67_, v_cases_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim___redArg(lean_object* v_t_71_, lean_object* v_intro_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_71_, v_intro_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim(lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_intro_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_75_, v_intro_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim___redArg(lean_object* v_t_79_, lean_object* v_infer_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_79_, v_infer_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim(lean_object* v_motive_82_, lean_object* v_t_83_, lean_object* v_h_84_, lean_object* v_infer_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_83_, v_infer_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim___redArg(lean_object* v_t_87_, lean_object* v_ext_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_87_, v_ext_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim(lean_object* v_motive_90_, lean_object* v_t_91_, lean_object* v_h_92_, lean_object* v_ext_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_91_, v_ext_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim___redArg(lean_object* v_t_95_, lean_object* v_symbol_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_95_, v_symbol_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim(lean_object* v_motive_98_, lean_object* v_t_99_, lean_object* v_h_100_, lean_object* v_symbol_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_99_, v_symbol_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim___redArg(lean_object* v_t_103_, lean_object* v_inj_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_103_, v_inj_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim(lean_object* v_motive_106_, lean_object* v_t_107_, lean_object* v_h_108_, lean_object* v_inj_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_107_, v_inj_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim___redArg(lean_object* v_t_111_, lean_object* v_funCC_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_111_, v_funCC_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim(lean_object* v_motive_114_, lean_object* v_t_115_, lean_object* v_h_116_, lean_object* v_funCC_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_115_, v_funCC_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim___redArg(lean_object* v_t_119_, lean_object* v_norm_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_119_, v_norm_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim(lean_object* v_motive_122_, lean_object* v_t_123_, lean_object* v_h_124_, lean_object* v_norm_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_123_, v_norm_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim___redArg(lean_object* v_t_127_, lean_object* v_unfold_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_127_, v_unfold_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim(lean_object* v_motive_130_, lean_object* v_t_131_, lean_object* v_h_132_, lean_object* v_unfold_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_131_, v_unfold_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim___redArg(lean_object* v_t_135_, lean_object* v_homo_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_135_, v_homo_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim(lean_object* v_motive_138_, lean_object* v_t_139_, lean_object* v_h_140_, lean_object* v_homo_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_139_, v_homo_141_);
return v___x_142_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_143_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_146_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1);
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
lean_ctor_set(v___x_148_, 2, v___x_147_);
lean_ctor_set(v___x_148_, 3, v___x_147_);
lean_ctor_set(v___x_148_, 4, v___x_146_);
lean_ctor_set(v___x_148_, 5, v___x_146_);
lean_ctor_set(v___x_148_, 6, v___x_146_);
lean_ctor_set(v___x_148_, 7, v___x_146_);
lean_ctor_set(v___x_148_, 8, v___x_146_);
lean_ctor_set(v___x_148_, 9, v___x_146_);
return v___x_148_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_unsigned_to_nat(32u);
v___x_150_ = lean_mk_empty_array_with_capacity(v___x_149_);
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_152_ = ((size_t)5ULL);
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = lean_unsigned_to_nat(32u);
v___x_155_ = lean_mk_empty_array_with_capacity(v___x_154_);
v___x_156_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_157_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v___x_155_);
lean_ctor_set(v___x_157_, 2, v___x_153_);
lean_ctor_set(v___x_157_, 3, v___x_153_);
lean_ctor_set_usize(v___x_157_, 4, v___x_152_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_158_ = lean_box(1);
v___x_159_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_160_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1);
v___x_161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v___x_159_);
lean_ctor_set(v___x_161_, 2, v___x_158_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(lean_object* v_msgData_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v___x_166_; lean_object* v_env_167_; lean_object* v_options_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_166_ = lean_st_ref_get(v___y_164_);
v_env_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc_ref(v_env_167_);
lean_dec(v___x_166_);
v_options_168_ = lean_ctor_get(v___y_163_, 2);
v___x_169_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2);
v___x_170_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_168_);
v___x_171_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_171_, 0, v_env_167_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
lean_ctor_set(v___x_171_, 2, v___x_170_);
lean_ctor_set(v___x_171_, 3, v_options_168_);
v___x_172_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v_msgData_162_);
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___boxed(lean_object* v_msgData_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msgData_174_, v___y_175_, v___y_176_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(lean_object* v_msg_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_ref_183_; lean_object* v___x_184_; lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_193_; 
v_ref_183_ = lean_ctor_get(v___y_180_, 5);
v___x_184_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_179_, v___y_180_, v___y_181_);
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_193_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_191_; 
lean_inc(v_ref_183_);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v_ref_183_);
lean_ctor_set(v___x_189_, 1, v_a_185_);
if (v_isShared_188_ == 0)
{
lean_ctor_set_tag(v___x_187_, 1);
lean_ctor_set(v___x_187_, 0, v___x_189_);
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg___boxed(lean_object* v_msg_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_194_, v___y_195_, v___y_196_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(lean_object* v_ref_199_, lean_object* v_msg_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_fileName_204_; lean_object* v_fileMap_205_; lean_object* v_options_206_; lean_object* v_currRecDepth_207_; lean_object* v_maxRecDepth_208_; lean_object* v_ref_209_; lean_object* v_currNamespace_210_; lean_object* v_openDecls_211_; lean_object* v_initHeartbeats_212_; lean_object* v_maxHeartbeats_213_; lean_object* v_quotContext_214_; lean_object* v_currMacroScope_215_; uint8_t v_diag_216_; lean_object* v_cancelTk_x3f_217_; uint8_t v_suppressElabErrors_218_; lean_object* v_inheritedTraceOptions_219_; lean_object* v_ref_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_fileName_204_ = lean_ctor_get(v___y_201_, 0);
v_fileMap_205_ = lean_ctor_get(v___y_201_, 1);
v_options_206_ = lean_ctor_get(v___y_201_, 2);
v_currRecDepth_207_ = lean_ctor_get(v___y_201_, 3);
v_maxRecDepth_208_ = lean_ctor_get(v___y_201_, 4);
v_ref_209_ = lean_ctor_get(v___y_201_, 5);
v_currNamespace_210_ = lean_ctor_get(v___y_201_, 6);
v_openDecls_211_ = lean_ctor_get(v___y_201_, 7);
v_initHeartbeats_212_ = lean_ctor_get(v___y_201_, 8);
v_maxHeartbeats_213_ = lean_ctor_get(v___y_201_, 9);
v_quotContext_214_ = lean_ctor_get(v___y_201_, 10);
v_currMacroScope_215_ = lean_ctor_get(v___y_201_, 11);
v_diag_216_ = lean_ctor_get_uint8(v___y_201_, sizeof(void*)*14);
v_cancelTk_x3f_217_ = lean_ctor_get(v___y_201_, 12);
v_suppressElabErrors_218_ = lean_ctor_get_uint8(v___y_201_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_219_ = lean_ctor_get(v___y_201_, 13);
v_ref_220_ = l_Lean_replaceRef(v_ref_199_, v_ref_209_);
lean_inc_ref(v_inheritedTraceOptions_219_);
lean_inc(v_cancelTk_x3f_217_);
lean_inc(v_currMacroScope_215_);
lean_inc(v_quotContext_214_);
lean_inc(v_maxHeartbeats_213_);
lean_inc(v_initHeartbeats_212_);
lean_inc(v_openDecls_211_);
lean_inc(v_currNamespace_210_);
lean_inc(v_maxRecDepth_208_);
lean_inc(v_currRecDepth_207_);
lean_inc_ref(v_options_206_);
lean_inc_ref(v_fileMap_205_);
lean_inc_ref(v_fileName_204_);
v___x_221_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_221_, 0, v_fileName_204_);
lean_ctor_set(v___x_221_, 1, v_fileMap_205_);
lean_ctor_set(v___x_221_, 2, v_options_206_);
lean_ctor_set(v___x_221_, 3, v_currRecDepth_207_);
lean_ctor_set(v___x_221_, 4, v_maxRecDepth_208_);
lean_ctor_set(v___x_221_, 5, v_ref_220_);
lean_ctor_set(v___x_221_, 6, v_currNamespace_210_);
lean_ctor_set(v___x_221_, 7, v_openDecls_211_);
lean_ctor_set(v___x_221_, 8, v_initHeartbeats_212_);
lean_ctor_set(v___x_221_, 9, v_maxHeartbeats_213_);
lean_ctor_set(v___x_221_, 10, v_quotContext_214_);
lean_ctor_set(v___x_221_, 11, v_currMacroScope_215_);
lean_ctor_set(v___x_221_, 12, v_cancelTk_x3f_217_);
lean_ctor_set(v___x_221_, 13, v_inheritedTraceOptions_219_);
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*14, v_diag_216_);
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*14 + 1, v_suppressElabErrors_218_);
v___x_222_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_200_, v___x_221_, v___y_202_);
lean_dec_ref_known(v___x_221_, 14);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg___boxed(lean_object* v_ref_223_, lean_object* v_msg_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_223_, v_msg_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v_ref_223_);
return v_res_228_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__4));
v___x_239_ = l_Lean_stringToMessageData(v___x_238_);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__6));
v___x_242_ = l_Lean_stringToMessageData(v___x_241_);
return v___x_242_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__51(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__50));
v___x_371_ = l_Lean_stringToMessageData(v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object* v_stx_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_403_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__3));
lean_inc(v_stx_399_);
v___x_404_ = l_Lean_Syntax_isOfKind(v_stx_399_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_405_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_406_ = l_Lean_MessageData_ofSyntax(v_stx_399_);
v___x_407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_405_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_409_, v_a_400_, v_a_401_);
return v___x_410_;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = l_Lean_Syntax_getArg(v_stx_399_, v___x_411_);
v___x_413_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__9));
lean_inc(v___x_412_);
v___x_414_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_415_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__11));
lean_inc(v___x_412_);
v___x_416_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_417_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__13));
lean_inc(v___x_412_);
v___x_418_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_419_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__15));
lean_inc(v___x_412_);
v___x_420_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_421_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__17));
lean_inc(v___x_412_);
v___x_422_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_423_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__19));
lean_inc(v___x_412_);
v___x_424_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_425_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__21));
lean_inc(v___x_412_);
v___x_426_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__23));
lean_inc(v___x_412_);
v___x_428_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_429_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__25));
lean_inc(v___x_412_);
v___x_430_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_429_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; uint8_t v___x_432_; 
v___x_431_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__27));
lean_inc(v___x_412_);
v___x_432_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_431_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_433_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
lean_inc(v___x_412_);
v___x_434_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_435_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__31));
lean_inc(v___x_412_);
v___x_436_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_437_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__33));
lean_inc(v___x_412_);
v___x_438_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_439_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__35));
lean_inc(v___x_412_);
v___x_440_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_439_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_441_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__37));
lean_inc(v___x_412_);
v___x_442_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_443_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__39));
lean_inc(v___x_412_);
v___x_444_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__41));
lean_inc(v___x_412_);
v___x_446_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_445_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_447_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__43));
lean_inc(v___x_412_);
v___x_448_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__45));
lean_inc(v___x_412_);
v___x_450_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_451_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__47));
lean_inc(v___x_412_);
v___x_452_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__49));
lean_inc(v___x_412_);
v___x_454_ = l_Lean_Syntax_isOfKind(v___x_412_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
lean_dec(v___x_412_);
v___x_455_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_456_ = l_Lean_MessageData_ofSyntax(v_stx_399_);
v___x_457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_455_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_459_, v_a_400_, v_a_401_);
return v___x_460_;
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec(v_stx_399_);
v___x_461_ = lean_unsigned_to_nat(1u);
v___x_462_ = l_Lean_Syntax_getArg(v___x_412_, v___x_461_);
lean_dec(v___x_412_);
v___x_463_ = l_Lean_Syntax_isNatLit_x3f(v___x_462_);
if (lean_obj_tag(v___x_463_) == 1)
{
lean_object* v_val_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_472_; 
lean_dec(v___x_462_);
v_val_464_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_472_ == 0)
{
v___x_466_ = v___x_463_;
v_isShared_467_ = v_isSharedCheck_472_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_val_464_);
lean_dec(v___x_463_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_472_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
lean_ctor_set_tag(v___x_466_, 5);
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_val_464_);
v___x_469_ = v_reuseFailAlloc_471_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; 
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
}
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec(v___x_463_);
v___x_473_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__51, &l_Lean_Meta_Grind_getAttrKindCore___closed__51_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__51);
v___x_474_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v___x_462_, v___x_473_, v_a_400_, v_a_401_);
lean_dec(v___x_462_);
return v___x_474_;
}
}
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec(v___x_412_);
lean_dec(v_stx_399_);
v___x_475_ = lean_box(10);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v___x_412_);
lean_dec(v_stx_399_);
v___x_477_ = lean_box(9);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = l_Lean_Syntax_getArg(v___x_412_, v___x_479_);
lean_inc(v___x_480_);
v___x_481_ = l_Lean_Syntax_matchesNull(v___x_480_, v___x_411_);
if (v___x_481_ == 0)
{
uint8_t v___x_482_; 
lean_inc(v___x_480_);
v___x_482_ = l_Lean_Syntax_matchesNull(v___x_480_, v___x_479_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec(v___x_480_);
lean_dec(v___x_412_);
v___x_483_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_484_ = l_Lean_MessageData_ofSyntax(v_stx_399_);
v___x_485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_483_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_485_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_487_, v_a_400_, v_a_401_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_489_ = l_Lean_Syntax_getArg(v___x_480_, v___x_411_);
lean_dec(v___x_480_);
v___x_490_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__54));
lean_inc(v___x_489_);
v___x_491_ = l_Lean_Syntax_isOfKind(v___x_489_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_492_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__56));
v___x_493_ = l_Lean_Syntax_isOfKind(v___x_489_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
lean_dec(v___x_412_);
v___x_494_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_495_ = l_Lean_MessageData_ofSyntax(v_stx_399_);
v___x_496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_496_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_498_, v_a_400_, v_a_401_);
return v___x_499_;
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_500_ = lean_unsigned_to_nat(2u);
v___x_501_ = l_Lean_Syntax_getArg(v___x_412_, v___x_500_);
lean_dec(v___x_412_);
lean_inc(v___x_501_);
v___x_502_ = l_Lean_Syntax_matchesNull(v___x_501_, v___x_411_);
if (v___x_502_ == 0)
{
uint8_t v___x_503_; 
v___x_503_ = l_Lean_Syntax_matchesNull(v___x_501_, v___x_479_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_504_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_505_ = l_Lean_MessageData_ofSyntax(v_stx_399_);
v___x_506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_506_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_508_, v_a_400_, v_a_401_);
return v___x_509_;
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec(v_stx_399_);
v___x_510_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_510_, 0, v___x_502_);
lean_ctor_set_uint8(v___x_510_, 1, v___x_404_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec(v___x_501_);
lean_dec(v_stx_399_);
v___x_512_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_512_, 0, v___x_491_);
lean_ctor_set_uint8(v___x_512_, 1, v___x_491_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
}
}
else
{
lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
lean_dec(v___x_489_);
v___x_514_ = lean_unsigned_to_nat(2u);
v___x_515_ = l_Lean_Syntax_getArg(v___x_412_, v___x_514_);
lean_dec(v___x_412_);
lean_inc(v___x_515_);
v___x_516_ = l_Lean_Syntax_matchesNull(v___x_515_, v___x_411_);
if (v___x_516_ == 0)
{
uint8_t v___x_517_; 
v___x_517_ = l_Lean_Syntax_matchesNull(v___x_515_, v___x_479_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_518_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_519_ = l_Lean_MessageData_ofSyntax(v_stx_399_);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_522_, v_a_400_, v_a_401_);
return v___x_523_;
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; 
lean_dec(v_stx_399_);
v___x_524_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_524_, 0, v___x_404_);
lean_ctor_set_uint8(v___x_524_, 1, v___x_404_);
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
return v___x_525_;
}
}
else
{
lean_object* v___x_526_; lean_object* v___x_527_; 
lean_dec(v___x_515_);
lean_dec(v_stx_399_);
v___x_526_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_526_, 0, v___x_404_);
lean_ctor_set_uint8(v___x_526_, 1, v___x_481_);
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
return v___x_527_;
}
}
}
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
lean_dec(v___x_480_);
v___x_528_ = lean_unsigned_to_nat(2u);
v___x_529_ = l_Lean_Syntax_getArg(v___x_412_, v___x_528_);
lean_dec(v___x_412_);
lean_inc(v___x_529_);
v___x_530_ = l_Lean_Syntax_matchesNull(v___x_529_, v___x_411_);
if (v___x_530_ == 0)
{
uint8_t v___x_531_; 
v___x_531_ = l_Lean_Syntax_matchesNull(v___x_529_, v___x_479_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_532_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_533_ = l_Lean_MessageData_ofSyntax(v_stx_399_);
v___x_534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_534_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_536_, v_a_400_, v_a_401_);
return v___x_537_;
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; 
lean_dec(v_stx_399_);
v___x_538_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_538_, 0, v___x_404_);
lean_ctor_set_uint8(v___x_538_, 1, v___x_404_);
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
}
else
{
lean_object* v___x_540_; lean_object* v___x_541_; 
lean_dec(v___x_529_);
lean_dec(v_stx_399_);
v___x_540_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_540_, 0, v___x_404_);
lean_ctor_set_uint8(v___x_540_, 1, v___x_446_);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
return v___x_541_;
}
}
}
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; 
lean_dec(v___x_412_);
lean_dec(v_stx_399_);
v___x_542_ = lean_box(7);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec(v___x_412_);
lean_dec(v_stx_399_);
v___x_544_ = lean_box(6);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; 
lean_dec(v___x_412_);
lean_dec(v_stx_399_);
v___x_546_ = lean_box(4);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec(v___x_412_);
lean_dec(v_stx_399_);
v___x_548_ = lean_box(2);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec(v___x_412_);
lean_dec(v_stx_399_);
v___x_550_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_550_, 0, v___x_404_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; 
lean_dec(v___x_412_);
lean_dec(v_stx_399_);
v___x_552_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_552_, 0, v___x_434_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
return v___x_553_;
}
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec(v___x_412_);
lean_dec(v_stx_399_);
v___x_554_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_554_, 0, v___x_404_);
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec(v___x_412_);
lean_dec(v_stx_399_);
v___x_557_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__57));
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec(v___x_412_);
lean_dec(v_stx_399_);
v___x_559_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__58));
v___x_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
return v___x_560_;
}
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v___x_412_);
lean_dec(v_stx_399_);
v___x_561_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__59));
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec(v___x_412_);
lean_dec(v_stx_399_);
v___x_563_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__60));
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_565_ = lean_unsigned_to_nat(3u);
v___x_566_ = l_Lean_Syntax_getArg(v___x_412_, v___x_565_);
lean_dec(v___x_412_);
lean_inc(v___x_566_);
v___x_567_ = l_Lean_Syntax_matchesNull(v___x_566_, v___x_411_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_566_);
v___x_569_ = l_Lean_Syntax_matchesNull(v___x_566_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
lean_dec(v___x_566_);
v___x_570_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_571_ = l_Lean_MessageData_ofSyntax(v_stx_399_);
v___x_572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_572_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_574_, v_a_400_, v_a_401_);
return v___x_575_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_576_ = l_Lean_Syntax_getArg(v___x_566_, v___x_411_);
lean_dec(v___x_566_);
v___x_577_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_578_ = l_Lean_Syntax_isOfKind(v___x_576_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_579_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_580_ = l_Lean_MessageData_ofSyntax(v_stx_399_);
v___x_581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_583_, v_a_400_, v_a_401_);
return v___x_584_;
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v_stx_399_);
v___x_585_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_585_, 0, v___x_404_);
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
return v___x_587_;
}
}
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
lean_dec(v___x_566_);
lean_dec(v_stx_399_);
v___x_588_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_588_, 0, v___x_422_);
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
}
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_591_ = lean_unsigned_to_nat(2u);
v___x_592_ = l_Lean_Syntax_getArg(v___x_412_, v___x_591_);
lean_dec(v___x_412_);
lean_inc(v___x_592_);
v___x_593_ = l_Lean_Syntax_matchesNull(v___x_592_, v___x_411_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_592_);
v___x_595_ = l_Lean_Syntax_matchesNull(v___x_592_, v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec(v___x_592_);
v___x_596_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_597_ = l_Lean_MessageData_ofSyntax(v_stx_399_);
v___x_598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_600_, v_a_400_, v_a_401_);
return v___x_601_;
}
else
{
lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_602_ = l_Lean_Syntax_getArg(v___x_592_, v___x_411_);
lean_dec(v___x_592_);
v___x_603_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_604_ = l_Lean_Syntax_isOfKind(v___x_602_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_605_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_606_ = l_Lean_MessageData_ofSyntax(v_stx_399_);
v___x_607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_607_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_609_, v_a_400_, v_a_401_);
return v___x_610_;
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec(v_stx_399_);
v___x_611_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_611_, 0, v___x_404_);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
}
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
lean_dec(v___x_592_);
lean_dec(v_stx_399_);
v___x_614_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_614_, 0, v___x_420_);
v___x_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
v___x_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
return v___x_616_;
}
}
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_617_ = lean_unsigned_to_nat(1u);
v___x_618_ = l_Lean_Syntax_getArg(v___x_412_, v___x_617_);
lean_dec(v___x_412_);
lean_inc(v___x_618_);
v___x_619_ = l_Lean_Syntax_matchesNull(v___x_618_, v___x_411_);
if (v___x_619_ == 0)
{
uint8_t v___x_620_; 
lean_inc(v___x_618_);
v___x_620_ = l_Lean_Syntax_matchesNull(v___x_618_, v___x_617_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec(v___x_618_);
v___x_621_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_622_ = l_Lean_MessageData_ofSyntax(v_stx_399_);
v___x_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_625_, v_a_400_, v_a_401_);
return v___x_626_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_627_ = l_Lean_Syntax_getArg(v___x_618_, v___x_411_);
lean_dec(v___x_618_);
v___x_628_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_629_ = l_Lean_Syntax_isOfKind(v___x_627_, v___x_628_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_630_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_631_ = l_Lean_MessageData_ofSyntax(v_stx_399_);
v___x_632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_634_, v_a_400_, v_a_401_);
return v___x_635_;
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
lean_dec(v_stx_399_);
v___x_636_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_636_, 0, v___x_404_);
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
}
}
else
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec(v___x_618_);
lean_dec(v_stx_399_);
v___x_639_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_639_, 0, v___x_418_);
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
}
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; 
lean_dec(v___x_412_);
lean_dec(v_stx_399_);
v___x_642_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__61));
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = l_Lean_Syntax_getArg(v___x_412_, v___x_644_);
lean_dec(v___x_412_);
lean_inc(v___x_645_);
v___x_646_ = l_Lean_Syntax_matchesNull(v___x_645_, v___x_411_);
if (v___x_646_ == 0)
{
uint8_t v___x_647_; 
lean_inc(v___x_645_);
v___x_647_ = l_Lean_Syntax_matchesNull(v___x_645_, v___x_644_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec(v___x_645_);
v___x_648_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_649_ = l_Lean_MessageData_ofSyntax(v_stx_399_);
v___x_650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_648_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___x_651_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_652_, v_a_400_, v_a_401_);
return v___x_653_;
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_654_ = l_Lean_Syntax_getArg(v___x_645_, v___x_411_);
lean_dec(v___x_645_);
v___x_655_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_656_ = l_Lean_Syntax_isOfKind(v___x_654_, v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_657_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_658_ = l_Lean_MessageData_ofSyntax(v_stx_399_);
v___x_659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_657_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_661_, v_a_400_, v_a_401_);
return v___x_662_;
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
lean_dec(v_stx_399_);
v___x_663_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_663_, 0, v___x_404_);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
return v___x_665_;
}
}
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec(v___x_645_);
lean_dec(v_stx_399_);
v___x_666_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_666_, 0, v___x_414_);
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
}
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_669_ = lean_unsigned_to_nat(1u);
v___x_670_ = l_Lean_Syntax_getArg(v___x_412_, v___x_669_);
lean_dec(v___x_412_);
lean_inc(v___x_670_);
v___x_671_ = l_Lean_Syntax_matchesNull(v___x_670_, v___x_411_);
if (v___x_671_ == 0)
{
uint8_t v___x_672_; 
lean_inc(v___x_670_);
v___x_672_ = l_Lean_Syntax_matchesNull(v___x_670_, v___x_669_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
lean_dec(v___x_670_);
v___x_673_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_674_ = l_Lean_MessageData_ofSyntax(v_stx_399_);
v___x_675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_673_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_675_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v___x_678_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_677_, v_a_400_, v_a_401_);
return v___x_678_;
}
else
{
lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_679_ = l_Lean_Syntax_getArg(v___x_670_, v___x_411_);
lean_dec(v___x_670_);
v___x_680_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_681_ = l_Lean_Syntax_isOfKind(v___x_679_, v___x_680_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_682_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_683_ = l_Lean_MessageData_ofSyntax(v_stx_399_);
v___x_684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_682_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_684_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_686_, v_a_400_, v_a_401_);
return v___x_687_;
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
lean_dec(v_stx_399_);
v___x_688_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_688_, 0, v___x_404_);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
}
}
else
{
lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec(v___x_670_);
lean_dec(v_stx_399_);
v___x_691_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__63));
v___x_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object* v_stx_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_Meta_Grind_getAttrKindCore(v_stx_693_, v_a_694_, v_a_695_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object* v_00_u03b1_698_, lean_object* v_msg_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_699_, v___y_700_, v___y_701_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object* v_00_u03b1_704_, lean_object* v_msg_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(v_00_u03b1_704_, v_msg_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object* v_00_u03b1_710_, lean_object* v_ref_711_, lean_object* v_msg_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_711_, v_msg_712_, v___y_713_, v___y_714_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object* v_00_u03b1_717_, lean_object* v_ref_718_, lean_object* v_msg_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(v_00_u03b1_717_, v_ref_718_, v_msg_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v_ref_718_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object* v_stx_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_728_ = lean_unsigned_to_nat(1u);
v___x_729_ = l_Lean_Syntax_getArg(v_stx_724_, v___x_728_);
v___x_730_ = l_Lean_Syntax_isNone(v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_731_ = lean_unsigned_to_nat(0u);
v___x_732_ = l_Lean_Syntax_getArg(v___x_729_, v___x_731_);
lean_dec(v___x_729_);
v___x_733_ = l_Lean_Meta_Grind_getAttrKindCore(v___x_732_, v_a_725_, v_a_726_);
return v___x_733_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; 
lean_dec(v___x_729_);
v___x_734_ = lean_box(3);
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
return v___x_735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object* v_stx_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_736_, v_a_737_, v_a_738_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_stx_736_);
return v_res_740_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = ((lean_object*)(l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0));
v___x_743_ = l_Lean_stringToMessageData(v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_obj_once(&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1, &l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once, _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1);
v___x_748_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_747_, v_a_744_, v_a_745_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_749_, v_a_750_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object* v_00_u03b1_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_754_, v_a_755_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object* v_00_u03b1_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_Meta_Grind_throwInvalidUsrModifier(v_00_u03b1_758_, v_a_759_, v_a_760_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
return v_res_762_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_763_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0);
v___x_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
return v___x_765_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object* v_ext_768_, lean_object* v_b_769_, uint8_t v_kind_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v_currNamespace_774_; lean_object* v___x_775_; lean_object* v_env_776_; lean_object* v_nextMacroScope_777_; lean_object* v_ngen_778_; lean_object* v_auxDeclNGen_779_; lean_object* v_traceState_780_; lean_object* v_messages_781_; lean_object* v_infoState_782_; lean_object* v_snapshotTasks_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_795_; 
v_currNamespace_774_ = lean_ctor_get(v___y_771_, 6);
v___x_775_ = lean_st_ref_take(v___y_772_);
v_env_776_ = lean_ctor_get(v___x_775_, 0);
v_nextMacroScope_777_ = lean_ctor_get(v___x_775_, 1);
v_ngen_778_ = lean_ctor_get(v___x_775_, 2);
v_auxDeclNGen_779_ = lean_ctor_get(v___x_775_, 3);
v_traceState_780_ = lean_ctor_get(v___x_775_, 4);
v_messages_781_ = lean_ctor_get(v___x_775_, 6);
v_infoState_782_ = lean_ctor_get(v___x_775_, 7);
v_snapshotTasks_783_ = lean_ctor_get(v___x_775_, 8);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; 
v_unused_796_ = lean_ctor_get(v___x_775_, 5);
lean_dec(v_unused_796_);
v___x_785_ = v___x_775_;
v_isShared_786_ = v_isSharedCheck_795_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_snapshotTasks_783_);
lean_inc(v_infoState_782_);
lean_inc(v_messages_781_);
lean_inc(v_traceState_780_);
lean_inc(v_auxDeclNGen_779_);
lean_inc(v_ngen_778_);
lean_inc(v_nextMacroScope_777_);
lean_inc(v_env_776_);
lean_dec(v___x_775_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_795_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
lean_inc(v_currNamespace_774_);
v___x_787_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_776_, v_ext_768_, v_b_769_, v_kind_770_, v_currNamespace_774_);
v___x_788_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 5, v___x_788_);
lean_ctor_set(v___x_785_, 0, v___x_787_);
v___x_790_ = v___x_785_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_nextMacroScope_777_);
lean_ctor_set(v_reuseFailAlloc_794_, 2, v_ngen_778_);
lean_ctor_set(v_reuseFailAlloc_794_, 3, v_auxDeclNGen_779_);
lean_ctor_set(v_reuseFailAlloc_794_, 4, v_traceState_780_);
lean_ctor_set(v_reuseFailAlloc_794_, 5, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_794_, 6, v_messages_781_);
lean_ctor_set(v_reuseFailAlloc_794_, 7, v_infoState_782_);
lean_ctor_set(v_reuseFailAlloc_794_, 8, v_snapshotTasks_783_);
v___x_790_ = v_reuseFailAlloc_794_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_791_ = lean_st_ref_set(v___y_772_, v___x_790_);
v___x_792_ = lean_box(0);
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
return v___x_793_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object* v_ext_797_, lean_object* v_b_798_, lean_object* v_kind_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
uint8_t v_kind_boxed_803_; lean_object* v_res_804_; 
v_kind_boxed_803_ = lean_unbox(v_kind_799_);
v_res_804_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_797_, v_b_798_, v_kind_boxed_803_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object* v_00_u03b1_805_, lean_object* v_00_u03b2_806_, lean_object* v_00_u03c3_807_, lean_object* v_ext_808_, lean_object* v_b_809_, uint8_t v_kind_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_808_, v_b_809_, v_kind_810_, v___y_811_, v___y_812_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object* v_00_u03b1_815_, lean_object* v_00_u03b2_816_, lean_object* v_00_u03c3_817_, lean_object* v_ext_818_, lean_object* v_b_819_, lean_object* v_kind_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
uint8_t v_kind_boxed_824_; lean_object* v_res_825_; 
v_kind_boxed_824_ = lean_unbox(v_kind_820_);
v_res_825_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(v_00_u03b1_815_, v_00_u03b2_816_, v_00_u03c3_817_, v_ext_818_, v_b_819_, v_kind_boxed_824_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object* v_ext_826_, lean_object* v_declName_827_, uint8_t v_eager_828_, uint8_t v_attrKind_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v___x_833_; 
lean_inc(v_declName_827_);
v___x_833_ = l_Lean_Meta_Grind_validateCasesAttr(v_declName_827_, v_eager_828_, v_a_830_, v_a_831_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec_ref_known(v___x_833_, 1);
v___x_834_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_834_, 0, v_declName_827_);
lean_ctor_set_uint8(v___x_834_, sizeof(void*)*1, v_eager_828_);
v___x_835_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_826_, v___x_834_, v_attrKind_829_, v_a_830_, v_a_831_);
return v___x_835_;
}
else
{
lean_dec(v_declName_827_);
lean_dec_ref(v_ext_826_);
return v___x_833_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object* v_ext_836_, lean_object* v_declName_837_, lean_object* v_eager_838_, lean_object* v_attrKind_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
uint8_t v_eager_boxed_843_; uint8_t v_attrKind_boxed_844_; lean_object* v_res_845_; 
v_eager_boxed_843_ = lean_unbox(v_eager_838_);
v_attrKind_boxed_844_ = lean_unbox(v_attrKind_839_);
v_res_845_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_836_, v_declName_837_, v_eager_boxed_843_, v_attrKind_boxed_844_, v_a_840_, v_a_841_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object* v_ext_846_, lean_object* v_declName_847_, uint8_t v_attrKind_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v___x_852_; 
lean_inc(v_declName_847_);
v___x_852_ = l_Lean_Meta_Grind_validateExtAttr(v_declName_847_, v_a_849_, v_a_850_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_860_; 
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; 
v_unused_861_ = lean_ctor_get(v___x_852_, 0);
lean_dec(v_unused_861_);
v___x_854_ = v___x_852_;
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
else
{
lean_dec(v___x_852_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v_declName_847_);
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_declName_847_);
v___x_857_ = v_reuseFailAlloc_859_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_846_, v___x_857_, v_attrKind_848_, v_a_849_, v_a_850_);
return v___x_858_;
}
}
}
else
{
lean_dec(v_declName_847_);
lean_dec_ref(v_ext_846_);
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object* v_ext_862_, lean_object* v_declName_863_, lean_object* v_attrKind_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
uint8_t v_attrKind_boxed_868_; lean_object* v_res_869_; 
v_attrKind_boxed_868_ = lean_unbox(v_attrKind_864_);
v_res_869_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_862_, v_declName_863_, v_attrKind_boxed_868_, v_a_865_, v_a_866_);
lean_dec(v_a_866_);
lean_dec_ref(v_a_865_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object* v_ext_870_, lean_object* v_declName_871_, uint8_t v_attrKind_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_876_, 0, v_declName_871_);
v___x_877_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_870_, v___x_876_, v_attrKind_872_, v_a_873_, v_a_874_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object* v_ext_878_, lean_object* v_declName_879_, lean_object* v_attrKind_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
uint8_t v_attrKind_boxed_884_; lean_object* v_res_885_; 
v_attrKind_boxed_884_ = lean_unbox(v_attrKind_880_);
v_res_885_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_878_, v_declName_879_, v_attrKind_boxed_884_, v_a_881_, v_a_882_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object* v_a_886_, lean_object* v_s_887_){
_start:
{
lean_object* v_casesTypes_888_; lean_object* v_funCC_889_; lean_object* v_ematch_890_; lean_object* v_inj_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
v_casesTypes_888_ = lean_ctor_get(v_s_887_, 0);
v_funCC_889_ = lean_ctor_get(v_s_887_, 2);
v_ematch_890_ = lean_ctor_get(v_s_887_, 3);
v_inj_891_ = lean_ctor_get(v_s_887_, 4);
v_isSharedCheck_898_ = !lean_is_exclusive(v_s_887_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v_s_887_, 1);
lean_dec(v_unused_899_);
v___x_893_ = v_s_887_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_inj_891_);
lean_inc(v_ematch_890_);
lean_inc(v_funCC_889_);
lean_inc(v_casesTypes_888_);
lean_dec(v_s_887_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 1, v_a_886_);
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_casesTypes_888_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_a_886_);
lean_ctor_set(v_reuseFailAlloc_897_, 2, v_funCC_889_);
lean_ctor_set(v_reuseFailAlloc_897_, 3, v_ematch_890_);
lean_ctor_set(v_reuseFailAlloc_897_, 4, v_inj_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object* v_ext_900_, lean_object* v_declName_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v___x_905_; lean_object* v_ext_906_; lean_object* v_toEnvExtension_907_; lean_object* v_env_908_; lean_object* v_asyncMode_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v_extThms_912_; lean_object* v___x_913_; 
v___x_905_ = lean_st_ref_get(v_a_903_);
v_ext_906_ = lean_ctor_get(v_ext_900_, 1);
v_toEnvExtension_907_ = lean_ctor_get(v_ext_906_, 0);
v_env_908_ = lean_ctor_get(v___x_905_, 0);
lean_inc_ref(v_env_908_);
lean_dec(v___x_905_);
v_asyncMode_909_ = lean_ctor_get(v_toEnvExtension_907_, 2);
v___x_910_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_911_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_910_, v_ext_900_, v_env_908_, v_asyncMode_909_);
v_extThms_912_ = lean_ctor_get(v___x_911_, 1);
lean_inc_ref(v_extThms_912_);
lean_dec(v___x_911_);
v___x_913_ = l_Lean_Meta_Grind_ExtTheorems_eraseDecl(v_extThms_912_, v_declName_901_, v_a_902_, v_a_903_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_943_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_943_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_943_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_943_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v_env_919_; lean_object* v_nextMacroScope_920_; lean_object* v_ngen_921_; lean_object* v_auxDeclNGen_922_; lean_object* v_traceState_923_; lean_object* v_messages_924_; lean_object* v_infoState_925_; lean_object* v_snapshotTasks_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_941_; 
v___x_918_ = lean_st_ref_take(v_a_903_);
v_env_919_ = lean_ctor_get(v___x_918_, 0);
v_nextMacroScope_920_ = lean_ctor_get(v___x_918_, 1);
v_ngen_921_ = lean_ctor_get(v___x_918_, 2);
v_auxDeclNGen_922_ = lean_ctor_get(v___x_918_, 3);
v_traceState_923_ = lean_ctor_get(v___x_918_, 4);
v_messages_924_ = lean_ctor_get(v___x_918_, 6);
v_infoState_925_ = lean_ctor_get(v___x_918_, 7);
v_snapshotTasks_926_ = lean_ctor_get(v___x_918_, 8);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; 
v_unused_942_ = lean_ctor_get(v___x_918_, 5);
lean_dec(v_unused_942_);
v___x_928_ = v___x_918_;
v_isShared_929_ = v_isSharedCheck_941_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_snapshotTasks_926_);
lean_inc(v_infoState_925_);
lean_inc(v_messages_924_);
lean_inc(v_traceState_923_);
lean_inc(v_auxDeclNGen_922_);
lean_inc(v_ngen_921_);
lean_inc(v_nextMacroScope_920_);
lean_inc(v_env_919_);
lean_dec(v___x_918_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_941_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___f_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v___f_930_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0), 2, 1);
lean_closure_set(v___f_930_, 0, v_a_914_);
v___x_931_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_900_, v_env_919_, v___f_930_);
v___x_932_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 5, v___x_932_);
lean_ctor_set(v___x_928_, 0, v___x_931_);
v___x_934_ = v___x_928_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_940_, 1, v_nextMacroScope_920_);
lean_ctor_set(v_reuseFailAlloc_940_, 2, v_ngen_921_);
lean_ctor_set(v_reuseFailAlloc_940_, 3, v_auxDeclNGen_922_);
lean_ctor_set(v_reuseFailAlloc_940_, 4, v_traceState_923_);
lean_ctor_set(v_reuseFailAlloc_940_, 5, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_940_, 6, v_messages_924_);
lean_ctor_set(v_reuseFailAlloc_940_, 7, v_infoState_925_);
lean_ctor_set(v_reuseFailAlloc_940_, 8, v_snapshotTasks_926_);
v___x_934_ = v_reuseFailAlloc_940_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_935_ = lean_st_ref_set(v_a_903_, v___x_934_);
v___x_936_ = lean_box(0);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_936_);
v___x_938_ = v___x_916_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
}
else
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
lean_dec_ref(v_ext_900_);
v_a_944_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_913_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_913_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object* v_ext_952_, lean_object* v_declName_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_952_, v_declName_953_, v_a_954_, v_a_955_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object* v_a_958_, lean_object* v_s_959_){
_start:
{
lean_object* v_extThms_960_; lean_object* v_funCC_961_; lean_object* v_ematch_962_; lean_object* v_inj_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
v_extThms_960_ = lean_ctor_get(v_s_959_, 1);
v_funCC_961_ = lean_ctor_get(v_s_959_, 2);
v_ematch_962_ = lean_ctor_get(v_s_959_, 3);
v_inj_963_ = lean_ctor_get(v_s_959_, 4);
v_isSharedCheck_970_ = !lean_is_exclusive(v_s_959_);
if (v_isSharedCheck_970_ == 0)
{
lean_object* v_unused_971_; 
v_unused_971_ = lean_ctor_get(v_s_959_, 0);
lean_dec(v_unused_971_);
v___x_965_ = v_s_959_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_inj_963_);
lean_inc(v_ematch_962_);
lean_inc(v_funCC_961_);
lean_inc(v_extThms_960_);
lean_dec(v_s_959_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v_a_958_);
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_958_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v_extThms_960_);
lean_ctor_set(v_reuseFailAlloc_969_, 2, v_funCC_961_);
lean_ctor_set(v_reuseFailAlloc_969_, 3, v_ematch_962_);
lean_ctor_set(v_reuseFailAlloc_969_, 4, v_inj_963_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object* v_ext_972_, lean_object* v_declName_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
lean_object* v___x_977_; 
lean_inc(v_declName_973_);
v___x_977_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v___x_978_; lean_object* v_ext_979_; lean_object* v_toEnvExtension_980_; lean_object* v_env_981_; lean_object* v_asyncMode_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v_casesTypes_985_; lean_object* v___x_986_; 
lean_dec_ref_known(v___x_977_, 1);
v___x_978_ = lean_st_ref_get(v_a_975_);
v_ext_979_ = lean_ctor_get(v_ext_972_, 1);
v_toEnvExtension_980_ = lean_ctor_get(v_ext_979_, 0);
v_env_981_ = lean_ctor_get(v___x_978_, 0);
lean_inc_ref(v_env_981_);
lean_dec(v___x_978_);
v_asyncMode_982_ = lean_ctor_get(v_toEnvExtension_980_, 2);
v___x_983_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_984_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_983_, v_ext_972_, v_env_981_, v_asyncMode_982_);
v_casesTypes_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc_ref(v_casesTypes_985_);
lean_dec(v___x_984_);
v___x_986_ = l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_casesTypes_985_, v_declName_973_, v_a_974_, v_a_975_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1016_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_989_ = v___x_986_;
v_isShared_990_ = v_isSharedCheck_1016_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_986_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1016_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v_env_992_; lean_object* v_nextMacroScope_993_; lean_object* v_ngen_994_; lean_object* v_auxDeclNGen_995_; lean_object* v_traceState_996_; lean_object* v_messages_997_; lean_object* v_infoState_998_; lean_object* v_snapshotTasks_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1014_; 
v___x_991_ = lean_st_ref_take(v_a_975_);
v_env_992_ = lean_ctor_get(v___x_991_, 0);
v_nextMacroScope_993_ = lean_ctor_get(v___x_991_, 1);
v_ngen_994_ = lean_ctor_get(v___x_991_, 2);
v_auxDeclNGen_995_ = lean_ctor_get(v___x_991_, 3);
v_traceState_996_ = lean_ctor_get(v___x_991_, 4);
v_messages_997_ = lean_ctor_get(v___x_991_, 6);
v_infoState_998_ = lean_ctor_get(v___x_991_, 7);
v_snapshotTasks_999_ = lean_ctor_get(v___x_991_, 8);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1014_ == 0)
{
lean_object* v_unused_1015_; 
v_unused_1015_ = lean_ctor_get(v___x_991_, 5);
lean_dec(v_unused_1015_);
v___x_1001_ = v___x_991_;
v_isShared_1002_ = v_isSharedCheck_1014_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_snapshotTasks_999_);
lean_inc(v_infoState_998_);
lean_inc(v_messages_997_);
lean_inc(v_traceState_996_);
lean_inc(v_auxDeclNGen_995_);
lean_inc(v_ngen_994_);
lean_inc(v_nextMacroScope_993_);
lean_inc(v_env_992_);
lean_dec(v___x_991_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1014_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___f_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___f_1003_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0), 2, 1);
lean_closure_set(v___f_1003_, 0, v_a_987_);
v___x_1004_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_972_, v_env_992_, v___f_1003_);
v___x_1005_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 5, v___x_1005_);
lean_ctor_set(v___x_1001_, 0, v___x_1004_);
v___x_1007_ = v___x_1001_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_nextMacroScope_993_);
lean_ctor_set(v_reuseFailAlloc_1013_, 2, v_ngen_994_);
lean_ctor_set(v_reuseFailAlloc_1013_, 3, v_auxDeclNGen_995_);
lean_ctor_set(v_reuseFailAlloc_1013_, 4, v_traceState_996_);
lean_ctor_set(v_reuseFailAlloc_1013_, 5, v___x_1005_);
lean_ctor_set(v_reuseFailAlloc_1013_, 6, v_messages_997_);
lean_ctor_set(v_reuseFailAlloc_1013_, 7, v_infoState_998_);
lean_ctor_set(v_reuseFailAlloc_1013_, 8, v_snapshotTasks_999_);
v___x_1007_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1008_ = lean_st_ref_set(v_a_975_, v___x_1007_);
v___x_1009_ = lean_box(0);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_1009_);
v___x_1011_ = v___x_989_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec_ref(v_ext_972_);
v_a_1017_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_986_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_986_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
else
{
lean_dec(v_declName_973_);
lean_dec_ref(v_ext_972_);
return v___x_977_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object* v_ext_1025_, lean_object* v_declName_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_1025_, v_declName_1026_, v_a_1027_, v_a_1028_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object* v___x_1031_, lean_object* v_s_1032_){
_start:
{
lean_object* v_casesTypes_1033_; lean_object* v_extThms_1034_; lean_object* v_ematch_1035_; lean_object* v_inj_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
v_casesTypes_1033_ = lean_ctor_get(v_s_1032_, 0);
v_extThms_1034_ = lean_ctor_get(v_s_1032_, 1);
v_ematch_1035_ = lean_ctor_get(v_s_1032_, 3);
v_inj_1036_ = lean_ctor_get(v_s_1032_, 4);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_s_1032_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; 
v_unused_1044_ = lean_ctor_get(v_s_1032_, 2);
lean_dec(v_unused_1044_);
v___x_1038_ = v_s_1032_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_inj_1036_);
lean_inc(v_ematch_1035_);
lean_inc(v_extThms_1034_);
lean_inc(v_casesTypes_1033_);
lean_dec(v_s_1032_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 2, v___x_1031_);
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_casesTypes_1033_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_extThms_1034_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1042_, 3, v_ematch_1035_);
lean_ctor_set(v_reuseFailAlloc_1042_, 4, v_inj_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object* v_k_1045_, lean_object* v_t_1046_){
_start:
{
if (lean_obj_tag(v_t_1046_) == 0)
{
lean_object* v_k_1047_; lean_object* v_v_1048_; lean_object* v_l_1049_; lean_object* v_r_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1704_; 
v_k_1047_ = lean_ctor_get(v_t_1046_, 1);
v_v_1048_ = lean_ctor_get(v_t_1046_, 2);
v_l_1049_ = lean_ctor_get(v_t_1046_, 3);
v_r_1050_ = lean_ctor_get(v_t_1046_, 4);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_t_1046_);
if (v_isSharedCheck_1704_ == 0)
{
lean_object* v_unused_1705_; 
v_unused_1705_ = lean_ctor_get(v_t_1046_, 0);
lean_dec(v_unused_1705_);
v___x_1052_ = v_t_1046_;
v_isShared_1053_ = v_isSharedCheck_1704_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_r_1050_);
lean_inc(v_l_1049_);
lean_inc(v_v_1048_);
lean_inc(v_k_1047_);
lean_dec(v_t_1046_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1704_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
uint8_t v___x_1054_; 
v___x_1054_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1045_, v_k_1047_);
switch(v___x_1054_)
{
case 0:
{
lean_object* v_impl_1055_; lean_object* v___x_1056_; 
v_impl_1055_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1045_, v_l_1049_);
v___x_1056_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1055_) == 0)
{
if (lean_obj_tag(v_r_1050_) == 0)
{
lean_object* v_size_1057_; lean_object* v_size_1058_; lean_object* v_k_1059_; lean_object* v_v_1060_; lean_object* v_l_1061_; lean_object* v_r_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
v_size_1057_ = lean_ctor_get(v_impl_1055_, 0);
lean_inc(v_size_1057_);
v_size_1058_ = lean_ctor_get(v_r_1050_, 0);
v_k_1059_ = lean_ctor_get(v_r_1050_, 1);
v_v_1060_ = lean_ctor_get(v_r_1050_, 2);
v_l_1061_ = lean_ctor_get(v_r_1050_, 3);
lean_inc(v_l_1061_);
v_r_1062_ = lean_ctor_get(v_r_1050_, 4);
v___x_1063_ = lean_unsigned_to_nat(3u);
v___x_1064_ = lean_nat_mul(v___x_1063_, v_size_1057_);
v___x_1065_ = lean_nat_dec_lt(v___x_1064_, v_size_1058_);
lean_dec(v___x_1064_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1069_; 
lean_dec(v_l_1061_);
v___x_1066_ = lean_nat_add(v___x_1056_, v_size_1057_);
lean_dec(v_size_1057_);
v___x_1067_ = lean_nat_add(v___x_1066_, v_size_1058_);
lean_dec(v___x_1066_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 3, v_impl_1055_);
lean_ctor_set(v___x_1052_, 0, v___x_1067_);
v___x_1069_ = v___x_1052_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_k_1047_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v_v_1048_);
lean_ctor_set(v_reuseFailAlloc_1070_, 3, v_impl_1055_);
lean_ctor_set(v_reuseFailAlloc_1070_, 4, v_r_1050_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
else
{
lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1134_; 
lean_inc(v_r_1062_);
lean_inc(v_v_1060_);
lean_inc(v_k_1059_);
lean_inc(v_size_1058_);
v_isSharedCheck_1134_ = !lean_is_exclusive(v_r_1050_);
if (v_isSharedCheck_1134_ == 0)
{
lean_object* v_unused_1135_; lean_object* v_unused_1136_; lean_object* v_unused_1137_; lean_object* v_unused_1138_; lean_object* v_unused_1139_; 
v_unused_1135_ = lean_ctor_get(v_r_1050_, 4);
lean_dec(v_unused_1135_);
v_unused_1136_ = lean_ctor_get(v_r_1050_, 3);
lean_dec(v_unused_1136_);
v_unused_1137_ = lean_ctor_get(v_r_1050_, 2);
lean_dec(v_unused_1137_);
v_unused_1138_ = lean_ctor_get(v_r_1050_, 1);
lean_dec(v_unused_1138_);
v_unused_1139_ = lean_ctor_get(v_r_1050_, 0);
lean_dec(v_unused_1139_);
v___x_1072_ = v_r_1050_;
v_isShared_1073_ = v_isSharedCheck_1134_;
goto v_resetjp_1071_;
}
else
{
lean_dec(v_r_1050_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1134_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v_size_1074_; lean_object* v_k_1075_; lean_object* v_v_1076_; lean_object* v_l_1077_; lean_object* v_r_1078_; lean_object* v_size_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v_size_1074_ = lean_ctor_get(v_l_1061_, 0);
v_k_1075_ = lean_ctor_get(v_l_1061_, 1);
v_v_1076_ = lean_ctor_get(v_l_1061_, 2);
v_l_1077_ = lean_ctor_get(v_l_1061_, 3);
v_r_1078_ = lean_ctor_get(v_l_1061_, 4);
v_size_1079_ = lean_ctor_get(v_r_1062_, 0);
v___x_1080_ = lean_unsigned_to_nat(2u);
v___x_1081_ = lean_nat_mul(v___x_1080_, v_size_1079_);
v___x_1082_ = lean_nat_dec_lt(v_size_1074_, v___x_1081_);
lean_dec(v___x_1081_);
if (v___x_1082_ == 0)
{
lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1110_; 
lean_inc(v_r_1078_);
lean_inc(v_l_1077_);
lean_inc(v_v_1076_);
lean_inc(v_k_1075_);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_l_1061_);
if (v_isSharedCheck_1110_ == 0)
{
lean_object* v_unused_1111_; lean_object* v_unused_1112_; lean_object* v_unused_1113_; lean_object* v_unused_1114_; lean_object* v_unused_1115_; 
v_unused_1111_ = lean_ctor_get(v_l_1061_, 4);
lean_dec(v_unused_1111_);
v_unused_1112_ = lean_ctor_get(v_l_1061_, 3);
lean_dec(v_unused_1112_);
v_unused_1113_ = lean_ctor_get(v_l_1061_, 2);
lean_dec(v_unused_1113_);
v_unused_1114_ = lean_ctor_get(v_l_1061_, 1);
lean_dec(v_unused_1114_);
v_unused_1115_ = lean_ctor_get(v_l_1061_, 0);
lean_dec(v_unused_1115_);
v___x_1084_ = v_l_1061_;
v_isShared_1085_ = v_isSharedCheck_1110_;
goto v_resetjp_1083_;
}
else
{
lean_dec(v_l_1061_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1110_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1100_; 
v___x_1086_ = lean_nat_add(v___x_1056_, v_size_1057_);
lean_dec(v_size_1057_);
v___x_1087_ = lean_nat_add(v___x_1086_, v_size_1058_);
lean_dec(v_size_1058_);
if (lean_obj_tag(v_l_1077_) == 0)
{
lean_object* v_size_1108_; 
v_size_1108_ = lean_ctor_get(v_l_1077_, 0);
lean_inc(v_size_1108_);
v___y_1100_ = v_size_1108_;
goto v___jp_1099_;
}
else
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_unsigned_to_nat(0u);
v___y_1100_ = v___x_1109_;
goto v___jp_1099_;
}
v___jp_1088_:
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1092_ = lean_nat_add(v___y_1090_, v___y_1091_);
lean_dec(v___y_1091_);
lean_dec(v___y_1090_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 4, v_r_1062_);
lean_ctor_set(v___x_1084_, 3, v_r_1078_);
lean_ctor_set(v___x_1084_, 2, v_v_1060_);
lean_ctor_set(v___x_1084_, 1, v_k_1059_);
lean_ctor_set(v___x_1084_, 0, v___x_1092_);
v___x_1094_ = v___x_1084_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_k_1059_);
lean_ctor_set(v_reuseFailAlloc_1098_, 2, v_v_1060_);
lean_ctor_set(v_reuseFailAlloc_1098_, 3, v_r_1078_);
lean_ctor_set(v_reuseFailAlloc_1098_, 4, v_r_1062_);
v___x_1094_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
lean_object* v___x_1096_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 4, v___x_1094_);
lean_ctor_set(v___x_1072_, 3, v___y_1089_);
lean_ctor_set(v___x_1072_, 2, v_v_1076_);
lean_ctor_set(v___x_1072_, 1, v_k_1075_);
lean_ctor_set(v___x_1072_, 0, v___x_1087_);
v___x_1096_ = v___x_1072_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1087_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_k_1075_);
lean_ctor_set(v_reuseFailAlloc_1097_, 2, v_v_1076_);
lean_ctor_set(v_reuseFailAlloc_1097_, 3, v___y_1089_);
lean_ctor_set(v_reuseFailAlloc_1097_, 4, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
v___jp_1099_:
{
lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1101_ = lean_nat_add(v___x_1086_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec(v___x_1086_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 4, v_l_1077_);
lean_ctor_set(v___x_1052_, 3, v_impl_1055_);
lean_ctor_set(v___x_1052_, 0, v___x_1101_);
v___x_1103_ = v___x_1052_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_k_1047_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v_v_1048_);
lean_ctor_set(v_reuseFailAlloc_1107_, 3, v_impl_1055_);
lean_ctor_set(v_reuseFailAlloc_1107_, 4, v_l_1077_);
v___x_1103_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_nat_add(v___x_1056_, v_size_1079_);
if (lean_obj_tag(v_r_1078_) == 0)
{
lean_object* v_size_1105_; 
v_size_1105_ = lean_ctor_get(v_r_1078_, 0);
lean_inc(v_size_1105_);
v___y_1089_ = v___x_1103_;
v___y_1090_ = v___x_1104_;
v___y_1091_ = v_size_1105_;
goto v___jp_1088_;
}
else
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_unsigned_to_nat(0u);
v___y_1089_ = v___x_1103_;
v___y_1090_ = v___x_1104_;
v___y_1091_ = v___x_1106_;
goto v___jp_1088_;
}
}
}
}
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
lean_del_object(v___x_1052_);
v___x_1116_ = lean_nat_add(v___x_1056_, v_size_1057_);
lean_dec(v_size_1057_);
v___x_1117_ = lean_nat_add(v___x_1116_, v_size_1058_);
lean_dec(v_size_1058_);
v___x_1118_ = lean_nat_add(v___x_1116_, v_size_1074_);
lean_dec(v___x_1116_);
lean_inc_ref(v_impl_1055_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 4, v_l_1061_);
lean_ctor_set(v___x_1072_, 3, v_impl_1055_);
lean_ctor_set(v___x_1072_, 2, v_v_1048_);
lean_ctor_set(v___x_1072_, 1, v_k_1047_);
lean_ctor_set(v___x_1072_, 0, v___x_1118_);
v___x_1120_ = v___x_1072_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_k_1047_);
lean_ctor_set(v_reuseFailAlloc_1133_, 2, v_v_1048_);
lean_ctor_set(v_reuseFailAlloc_1133_, 3, v_impl_1055_);
lean_ctor_set(v_reuseFailAlloc_1133_, 4, v_l_1061_);
v___x_1120_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
v_isSharedCheck_1127_ = !lean_is_exclusive(v_impl_1055_);
if (v_isSharedCheck_1127_ == 0)
{
lean_object* v_unused_1128_; lean_object* v_unused_1129_; lean_object* v_unused_1130_; lean_object* v_unused_1131_; lean_object* v_unused_1132_; 
v_unused_1128_ = lean_ctor_get(v_impl_1055_, 4);
lean_dec(v_unused_1128_);
v_unused_1129_ = lean_ctor_get(v_impl_1055_, 3);
lean_dec(v_unused_1129_);
v_unused_1130_ = lean_ctor_get(v_impl_1055_, 2);
lean_dec(v_unused_1130_);
v_unused_1131_ = lean_ctor_get(v_impl_1055_, 1);
lean_dec(v_unused_1131_);
v_unused_1132_ = lean_ctor_get(v_impl_1055_, 0);
lean_dec(v_unused_1132_);
v___x_1122_ = v_impl_1055_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_dec(v_impl_1055_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 4, v_r_1062_);
lean_ctor_set(v___x_1122_, 3, v___x_1120_);
lean_ctor_set(v___x_1122_, 2, v_v_1060_);
lean_ctor_set(v___x_1122_, 1, v_k_1059_);
lean_ctor_set(v___x_1122_, 0, v___x_1117_);
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_k_1059_);
lean_ctor_set(v_reuseFailAlloc_1126_, 2, v_v_1060_);
lean_ctor_set(v_reuseFailAlloc_1126_, 3, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1126_, 4, v_r_1062_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; 
v_size_1140_ = lean_ctor_get(v_impl_1055_, 0);
lean_inc(v_size_1140_);
v___x_1141_ = lean_nat_add(v___x_1056_, v_size_1140_);
lean_dec(v_size_1140_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 3, v_impl_1055_);
lean_ctor_set(v___x_1052_, 0, v___x_1141_);
v___x_1143_ = v___x_1052_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_k_1047_);
lean_ctor_set(v_reuseFailAlloc_1144_, 2, v_v_1048_);
lean_ctor_set(v_reuseFailAlloc_1144_, 3, v_impl_1055_);
lean_ctor_set(v_reuseFailAlloc_1144_, 4, v_r_1050_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
else
{
if (lean_obj_tag(v_r_1050_) == 0)
{
lean_object* v_l_1145_; 
v_l_1145_ = lean_ctor_get(v_r_1050_, 3);
lean_inc(v_l_1145_);
if (lean_obj_tag(v_l_1145_) == 0)
{
lean_object* v_r_1146_; 
v_r_1146_ = lean_ctor_get(v_r_1050_, 4);
lean_inc(v_r_1146_);
if (lean_obj_tag(v_r_1146_) == 0)
{
lean_object* v_size_1147_; lean_object* v_k_1148_; lean_object* v_v_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1162_; 
v_size_1147_ = lean_ctor_get(v_r_1050_, 0);
v_k_1148_ = lean_ctor_get(v_r_1050_, 1);
v_v_1149_ = lean_ctor_get(v_r_1050_, 2);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_r_1050_);
if (v_isSharedCheck_1162_ == 0)
{
lean_object* v_unused_1163_; lean_object* v_unused_1164_; 
v_unused_1163_ = lean_ctor_get(v_r_1050_, 4);
lean_dec(v_unused_1163_);
v_unused_1164_ = lean_ctor_get(v_r_1050_, 3);
lean_dec(v_unused_1164_);
v___x_1151_ = v_r_1050_;
v_isShared_1152_ = v_isSharedCheck_1162_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_v_1149_);
lean_inc(v_k_1148_);
lean_inc(v_size_1147_);
lean_dec(v_r_1050_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1162_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v_size_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
v_size_1153_ = lean_ctor_get(v_l_1145_, 0);
v___x_1154_ = lean_nat_add(v___x_1056_, v_size_1147_);
lean_dec(v_size_1147_);
v___x_1155_ = lean_nat_add(v___x_1056_, v_size_1153_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 4, v_l_1145_);
lean_ctor_set(v___x_1151_, 3, v_impl_1055_);
lean_ctor_set(v___x_1151_, 2, v_v_1048_);
lean_ctor_set(v___x_1151_, 1, v_k_1047_);
lean_ctor_set(v___x_1151_, 0, v___x_1155_);
v___x_1157_ = v___x_1151_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_k_1047_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v_v_1048_);
lean_ctor_set(v_reuseFailAlloc_1161_, 3, v_impl_1055_);
lean_ctor_set(v_reuseFailAlloc_1161_, 4, v_l_1145_);
v___x_1157_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1159_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 4, v_r_1146_);
lean_ctor_set(v___x_1052_, 3, v___x_1157_);
lean_ctor_set(v___x_1052_, 2, v_v_1149_);
lean_ctor_set(v___x_1052_, 1, v_k_1148_);
lean_ctor_set(v___x_1052_, 0, v___x_1154_);
v___x_1159_ = v___x_1052_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_k_1148_);
lean_ctor_set(v_reuseFailAlloc_1160_, 2, v_v_1149_);
lean_ctor_set(v_reuseFailAlloc_1160_, 3, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1160_, 4, v_r_1146_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
else
{
lean_object* v_k_1165_; lean_object* v_v_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1189_; 
v_k_1165_ = lean_ctor_get(v_r_1050_, 1);
v_v_1166_ = lean_ctor_get(v_r_1050_, 2);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_r_1050_);
if (v_isSharedCheck_1189_ == 0)
{
lean_object* v_unused_1190_; lean_object* v_unused_1191_; lean_object* v_unused_1192_; 
v_unused_1190_ = lean_ctor_get(v_r_1050_, 4);
lean_dec(v_unused_1190_);
v_unused_1191_ = lean_ctor_get(v_r_1050_, 3);
lean_dec(v_unused_1191_);
v_unused_1192_ = lean_ctor_get(v_r_1050_, 0);
lean_dec(v_unused_1192_);
v___x_1168_ = v_r_1050_;
v_isShared_1169_ = v_isSharedCheck_1189_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_v_1166_);
lean_inc(v_k_1165_);
lean_dec(v_r_1050_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1189_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v_k_1170_; lean_object* v_v_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1185_; 
v_k_1170_ = lean_ctor_get(v_l_1145_, 1);
v_v_1171_ = lean_ctor_get(v_l_1145_, 2);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_l_1145_);
if (v_isSharedCheck_1185_ == 0)
{
lean_object* v_unused_1186_; lean_object* v_unused_1187_; lean_object* v_unused_1188_; 
v_unused_1186_ = lean_ctor_get(v_l_1145_, 4);
lean_dec(v_unused_1186_);
v_unused_1187_ = lean_ctor_get(v_l_1145_, 3);
lean_dec(v_unused_1187_);
v_unused_1188_ = lean_ctor_get(v_l_1145_, 0);
lean_dec(v_unused_1188_);
v___x_1173_ = v_l_1145_;
v_isShared_1174_ = v_isSharedCheck_1185_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_v_1171_);
lean_inc(v_k_1170_);
lean_dec(v_l_1145_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1185_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1175_ = lean_unsigned_to_nat(3u);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 4, v_r_1146_);
lean_ctor_set(v___x_1173_, 3, v_r_1146_);
lean_ctor_set(v___x_1173_, 2, v_v_1048_);
lean_ctor_set(v___x_1173_, 1, v_k_1047_);
lean_ctor_set(v___x_1173_, 0, v___x_1056_);
v___x_1177_ = v___x_1173_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_k_1047_);
lean_ctor_set(v_reuseFailAlloc_1184_, 2, v_v_1048_);
lean_ctor_set(v_reuseFailAlloc_1184_, 3, v_r_1146_);
lean_ctor_set(v_reuseFailAlloc_1184_, 4, v_r_1146_);
v___x_1177_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1179_; 
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 3, v_r_1146_);
lean_ctor_set(v___x_1168_, 0, v___x_1056_);
v___x_1179_ = v___x_1168_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_k_1165_);
lean_ctor_set(v_reuseFailAlloc_1183_, 2, v_v_1166_);
lean_ctor_set(v_reuseFailAlloc_1183_, 3, v_r_1146_);
lean_ctor_set(v_reuseFailAlloc_1183_, 4, v_r_1146_);
v___x_1179_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1181_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 4, v___x_1179_);
lean_ctor_set(v___x_1052_, 3, v___x_1177_);
lean_ctor_set(v___x_1052_, 2, v_v_1171_);
lean_ctor_set(v___x_1052_, 1, v_k_1170_);
lean_ctor_set(v___x_1052_, 0, v___x_1175_);
v___x_1181_ = v___x_1052_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_k_1170_);
lean_ctor_set(v_reuseFailAlloc_1182_, 2, v_v_1171_);
lean_ctor_set(v_reuseFailAlloc_1182_, 3, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1182_, 4, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1193_; 
v_r_1193_ = lean_ctor_get(v_r_1050_, 4);
lean_inc(v_r_1193_);
if (lean_obj_tag(v_r_1193_) == 0)
{
lean_object* v_k_1194_; lean_object* v_v_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1206_; 
v_k_1194_ = lean_ctor_get(v_r_1050_, 1);
v_v_1195_ = lean_ctor_get(v_r_1050_, 2);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_r_1050_);
if (v_isSharedCheck_1206_ == 0)
{
lean_object* v_unused_1207_; lean_object* v_unused_1208_; lean_object* v_unused_1209_; 
v_unused_1207_ = lean_ctor_get(v_r_1050_, 4);
lean_dec(v_unused_1207_);
v_unused_1208_ = lean_ctor_get(v_r_1050_, 3);
lean_dec(v_unused_1208_);
v_unused_1209_ = lean_ctor_get(v_r_1050_, 0);
lean_dec(v_unused_1209_);
v___x_1197_ = v_r_1050_;
v_isShared_1198_ = v_isSharedCheck_1206_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_v_1195_);
lean_inc(v_k_1194_);
lean_dec(v_r_1050_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1206_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1199_ = lean_unsigned_to_nat(3u);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 4, v_l_1145_);
lean_ctor_set(v___x_1197_, 2, v_v_1048_);
lean_ctor_set(v___x_1197_, 1, v_k_1047_);
lean_ctor_set(v___x_1197_, 0, v___x_1056_);
v___x_1201_ = v___x_1197_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_k_1047_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v_v_1048_);
lean_ctor_set(v_reuseFailAlloc_1205_, 3, v_l_1145_);
lean_ctor_set(v_reuseFailAlloc_1205_, 4, v_l_1145_);
v___x_1201_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1203_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 4, v_r_1193_);
lean_ctor_set(v___x_1052_, 3, v___x_1201_);
lean_ctor_set(v___x_1052_, 2, v_v_1195_);
lean_ctor_set(v___x_1052_, 1, v_k_1194_);
lean_ctor_set(v___x_1052_, 0, v___x_1199_);
v___x_1203_ = v___x_1052_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_k_1194_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v_v_1195_);
lean_ctor_set(v_reuseFailAlloc_1204_, 3, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1204_, 4, v_r_1193_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
else
{
lean_object* v_size_1210_; lean_object* v_k_1211_; lean_object* v_v_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1223_; 
v_size_1210_ = lean_ctor_get(v_r_1050_, 0);
v_k_1211_ = lean_ctor_get(v_r_1050_, 1);
v_v_1212_ = lean_ctor_get(v_r_1050_, 2);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_r_1050_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; lean_object* v_unused_1225_; 
v_unused_1224_ = lean_ctor_get(v_r_1050_, 4);
lean_dec(v_unused_1224_);
v_unused_1225_ = lean_ctor_get(v_r_1050_, 3);
lean_dec(v_unused_1225_);
v___x_1214_ = v_r_1050_;
v_isShared_1215_ = v_isSharedCheck_1223_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_v_1212_);
lean_inc(v_k_1211_);
lean_inc(v_size_1210_);
lean_dec(v_r_1050_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1223_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 3, v_r_1193_);
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_size_1210_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_k_1211_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v_v_1212_);
lean_ctor_set(v_reuseFailAlloc_1222_, 3, v_r_1193_);
lean_ctor_set(v_reuseFailAlloc_1222_, 4, v_r_1193_);
v___x_1217_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1218_ = lean_unsigned_to_nat(2u);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 4, v___x_1217_);
lean_ctor_set(v___x_1052_, 3, v_r_1193_);
lean_ctor_set(v___x_1052_, 0, v___x_1218_);
v___x_1220_ = v___x_1052_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_k_1047_);
lean_ctor_set(v_reuseFailAlloc_1221_, 2, v_v_1048_);
lean_ctor_set(v_reuseFailAlloc_1221_, 3, v_r_1193_);
lean_ctor_set(v_reuseFailAlloc_1221_, 4, v___x_1217_);
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
else
{
lean_object* v___x_1227_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 3, v_r_1050_);
lean_ctor_set(v___x_1052_, 0, v___x_1056_);
v___x_1227_ = v___x_1052_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_k_1047_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_v_1048_);
lean_ctor_set(v_reuseFailAlloc_1228_, 3, v_r_1050_);
lean_ctor_set(v_reuseFailAlloc_1228_, 4, v_r_1050_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1052_);
lean_dec(v_v_1048_);
lean_dec(v_k_1047_);
if (lean_obj_tag(v_l_1049_) == 0)
{
if (lean_obj_tag(v_r_1050_) == 0)
{
lean_object* v_size_1229_; lean_object* v_k_1230_; lean_object* v_v_1231_; lean_object* v_l_1232_; lean_object* v_r_1233_; lean_object* v_size_1234_; lean_object* v_k_1235_; lean_object* v_v_1236_; lean_object* v_l_1237_; lean_object* v_r_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; 
v_size_1229_ = lean_ctor_get(v_l_1049_, 0);
v_k_1230_ = lean_ctor_get(v_l_1049_, 1);
v_v_1231_ = lean_ctor_get(v_l_1049_, 2);
v_l_1232_ = lean_ctor_get(v_l_1049_, 3);
v_r_1233_ = lean_ctor_get(v_l_1049_, 4);
lean_inc(v_r_1233_);
v_size_1234_ = lean_ctor_get(v_r_1050_, 0);
v_k_1235_ = lean_ctor_get(v_r_1050_, 1);
v_v_1236_ = lean_ctor_get(v_r_1050_, 2);
v_l_1237_ = lean_ctor_get(v_r_1050_, 3);
lean_inc(v_l_1237_);
v_r_1238_ = lean_ctor_get(v_r_1050_, 4);
v___x_1239_ = lean_unsigned_to_nat(1u);
v___x_1240_ = lean_nat_dec_lt(v_size_1229_, v_size_1234_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1376_; 
lean_inc(v_l_1232_);
lean_inc(v_v_1231_);
lean_inc(v_k_1230_);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_l_1049_);
if (v_isSharedCheck_1376_ == 0)
{
lean_object* v_unused_1377_; lean_object* v_unused_1378_; lean_object* v_unused_1379_; lean_object* v_unused_1380_; lean_object* v_unused_1381_; 
v_unused_1377_ = lean_ctor_get(v_l_1049_, 4);
lean_dec(v_unused_1377_);
v_unused_1378_ = lean_ctor_get(v_l_1049_, 3);
lean_dec(v_unused_1378_);
v_unused_1379_ = lean_ctor_get(v_l_1049_, 2);
lean_dec(v_unused_1379_);
v_unused_1380_ = lean_ctor_get(v_l_1049_, 1);
lean_dec(v_unused_1380_);
v_unused_1381_ = lean_ctor_get(v_l_1049_, 0);
lean_dec(v_unused_1381_);
v___x_1242_ = v_l_1049_;
v_isShared_1243_ = v_isSharedCheck_1376_;
goto v_resetjp_1241_;
}
else
{
lean_dec(v_l_1049_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1376_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1244_; lean_object* v_tree_1245_; 
v___x_1244_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1230_, v_v_1231_, v_l_1232_, v_r_1233_);
v_tree_1245_ = lean_ctor_get(v___x_1244_, 2);
lean_inc(v_tree_1245_);
if (lean_obj_tag(v_tree_1245_) == 0)
{
lean_object* v_k_1246_; lean_object* v_v_1247_; lean_object* v_size_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v_k_1246_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_k_1246_);
v_v_1247_ = lean_ctor_get(v___x_1244_, 1);
lean_inc(v_v_1247_);
lean_dec_ref(v___x_1244_);
v_size_1248_ = lean_ctor_get(v_tree_1245_, 0);
v___x_1249_ = lean_unsigned_to_nat(3u);
v___x_1250_ = lean_nat_mul(v___x_1249_, v_size_1248_);
v___x_1251_ = lean_nat_dec_lt(v___x_1250_, v_size_1234_);
lean_dec(v___x_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1255_; 
lean_dec(v_l_1237_);
v___x_1252_ = lean_nat_add(v___x_1239_, v_size_1248_);
v___x_1253_ = lean_nat_add(v___x_1252_, v_size_1234_);
lean_dec(v___x_1252_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 4, v_r_1050_);
lean_ctor_set(v___x_1242_, 3, v_tree_1245_);
lean_ctor_set(v___x_1242_, 2, v_v_1247_);
lean_ctor_set(v___x_1242_, 1, v_k_1246_);
lean_ctor_set(v___x_1242_, 0, v___x_1253_);
v___x_1255_ = v___x_1242_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_k_1246_);
lean_ctor_set(v_reuseFailAlloc_1256_, 2, v_v_1247_);
lean_ctor_set(v_reuseFailAlloc_1256_, 3, v_tree_1245_);
lean_ctor_set(v_reuseFailAlloc_1256_, 4, v_r_1050_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
else
{
lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1311_; 
lean_inc(v_r_1238_);
lean_inc(v_v_1236_);
lean_inc(v_k_1235_);
lean_inc(v_size_1234_);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_r_1050_);
if (v_isSharedCheck_1311_ == 0)
{
lean_object* v_unused_1312_; lean_object* v_unused_1313_; lean_object* v_unused_1314_; lean_object* v_unused_1315_; lean_object* v_unused_1316_; 
v_unused_1312_ = lean_ctor_get(v_r_1050_, 4);
lean_dec(v_unused_1312_);
v_unused_1313_ = lean_ctor_get(v_r_1050_, 3);
lean_dec(v_unused_1313_);
v_unused_1314_ = lean_ctor_get(v_r_1050_, 2);
lean_dec(v_unused_1314_);
v_unused_1315_ = lean_ctor_get(v_r_1050_, 1);
lean_dec(v_unused_1315_);
v_unused_1316_ = lean_ctor_get(v_r_1050_, 0);
lean_dec(v_unused_1316_);
v___x_1258_ = v_r_1050_;
v_isShared_1259_ = v_isSharedCheck_1311_;
goto v_resetjp_1257_;
}
else
{
lean_dec(v_r_1050_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1311_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v_size_1260_; lean_object* v_k_1261_; lean_object* v_v_1262_; lean_object* v_l_1263_; lean_object* v_r_1264_; lean_object* v_size_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; uint8_t v___x_1268_; 
v_size_1260_ = lean_ctor_get(v_l_1237_, 0);
v_k_1261_ = lean_ctor_get(v_l_1237_, 1);
v_v_1262_ = lean_ctor_get(v_l_1237_, 2);
v_l_1263_ = lean_ctor_get(v_l_1237_, 3);
v_r_1264_ = lean_ctor_get(v_l_1237_, 4);
v_size_1265_ = lean_ctor_get(v_r_1238_, 0);
v___x_1266_ = lean_unsigned_to_nat(2u);
v___x_1267_ = lean_nat_mul(v___x_1266_, v_size_1265_);
v___x_1268_ = lean_nat_dec_lt(v_size_1260_, v___x_1267_);
lean_dec(v___x_1267_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1296_; 
lean_inc(v_r_1264_);
lean_inc(v_l_1263_);
lean_inc(v_v_1262_);
lean_inc(v_k_1261_);
v_isSharedCheck_1296_ = !lean_is_exclusive(v_l_1237_);
if (v_isSharedCheck_1296_ == 0)
{
lean_object* v_unused_1297_; lean_object* v_unused_1298_; lean_object* v_unused_1299_; lean_object* v_unused_1300_; lean_object* v_unused_1301_; 
v_unused_1297_ = lean_ctor_get(v_l_1237_, 4);
lean_dec(v_unused_1297_);
v_unused_1298_ = lean_ctor_get(v_l_1237_, 3);
lean_dec(v_unused_1298_);
v_unused_1299_ = lean_ctor_get(v_l_1237_, 2);
lean_dec(v_unused_1299_);
v_unused_1300_ = lean_ctor_get(v_l_1237_, 1);
lean_dec(v_unused_1300_);
v_unused_1301_ = lean_ctor_get(v_l_1237_, 0);
lean_dec(v_unused_1301_);
v___x_1270_ = v_l_1237_;
v_isShared_1271_ = v_isSharedCheck_1296_;
goto v_resetjp_1269_;
}
else
{
lean_dec(v_l_1237_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1296_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1286_; 
v___x_1272_ = lean_nat_add(v___x_1239_, v_size_1248_);
v___x_1273_ = lean_nat_add(v___x_1272_, v_size_1234_);
lean_dec(v_size_1234_);
if (lean_obj_tag(v_l_1263_) == 0)
{
lean_object* v_size_1294_; 
v_size_1294_ = lean_ctor_get(v_l_1263_, 0);
lean_inc(v_size_1294_);
v___y_1286_ = v_size_1294_;
goto v___jp_1285_;
}
else
{
lean_object* v___x_1295_; 
v___x_1295_ = lean_unsigned_to_nat(0u);
v___y_1286_ = v___x_1295_;
goto v___jp_1285_;
}
v___jp_1274_:
{
lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1278_ = lean_nat_add(v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec(v___y_1276_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 4, v_r_1238_);
lean_ctor_set(v___x_1270_, 3, v_r_1264_);
lean_ctor_set(v___x_1270_, 2, v_v_1236_);
lean_ctor_set(v___x_1270_, 1, v_k_1235_);
lean_ctor_set(v___x_1270_, 0, v___x_1278_);
v___x_1280_ = v___x_1270_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_k_1235_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v_v_1236_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v_r_1264_);
lean_ctor_set(v_reuseFailAlloc_1284_, 4, v_r_1238_);
v___x_1280_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1282_; 
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 4, v___x_1280_);
lean_ctor_set(v___x_1258_, 3, v___y_1275_);
lean_ctor_set(v___x_1258_, 2, v_v_1262_);
lean_ctor_set(v___x_1258_, 1, v_k_1261_);
lean_ctor_set(v___x_1258_, 0, v___x_1273_);
v___x_1282_ = v___x_1258_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1273_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_k_1261_);
lean_ctor_set(v_reuseFailAlloc_1283_, 2, v_v_1262_);
lean_ctor_set(v_reuseFailAlloc_1283_, 3, v___y_1275_);
lean_ctor_set(v_reuseFailAlloc_1283_, 4, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
v___jp_1285_:
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1287_ = lean_nat_add(v___x_1272_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec(v___x_1272_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 4, v_l_1263_);
lean_ctor_set(v___x_1242_, 3, v_tree_1245_);
lean_ctor_set(v___x_1242_, 2, v_v_1247_);
lean_ctor_set(v___x_1242_, 1, v_k_1246_);
lean_ctor_set(v___x_1242_, 0, v___x_1287_);
v___x_1289_ = v___x_1242_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_k_1246_);
lean_ctor_set(v_reuseFailAlloc_1293_, 2, v_v_1247_);
lean_ctor_set(v_reuseFailAlloc_1293_, 3, v_tree_1245_);
lean_ctor_set(v_reuseFailAlloc_1293_, 4, v_l_1263_);
v___x_1289_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1290_; 
v___x_1290_ = lean_nat_add(v___x_1239_, v_size_1265_);
if (lean_obj_tag(v_r_1264_) == 0)
{
lean_object* v_size_1291_; 
v_size_1291_ = lean_ctor_get(v_r_1264_, 0);
lean_inc(v_size_1291_);
v___y_1275_ = v___x_1289_;
v___y_1276_ = v___x_1290_;
v___y_1277_ = v_size_1291_;
goto v___jp_1274_;
}
else
{
lean_object* v___x_1292_; 
v___x_1292_ = lean_unsigned_to_nat(0u);
v___y_1275_ = v___x_1289_;
v___y_1276_ = v___x_1290_;
v___y_1277_ = v___x_1292_;
goto v___jp_1274_;
}
}
}
}
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1302_ = lean_nat_add(v___x_1239_, v_size_1248_);
v___x_1303_ = lean_nat_add(v___x_1302_, v_size_1234_);
lean_dec(v_size_1234_);
v___x_1304_ = lean_nat_add(v___x_1302_, v_size_1260_);
lean_dec(v___x_1302_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 4, v_l_1237_);
lean_ctor_set(v___x_1258_, 3, v_tree_1245_);
lean_ctor_set(v___x_1258_, 2, v_v_1247_);
lean_ctor_set(v___x_1258_, 1, v_k_1246_);
lean_ctor_set(v___x_1258_, 0, v___x_1304_);
v___x_1306_ = v___x_1258_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1304_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_k_1246_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v_v_1247_);
lean_ctor_set(v_reuseFailAlloc_1310_, 3, v_tree_1245_);
lean_ctor_set(v_reuseFailAlloc_1310_, 4, v_l_1237_);
v___x_1306_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1308_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 4, v_r_1238_);
lean_ctor_set(v___x_1242_, 3, v___x_1306_);
lean_ctor_set(v___x_1242_, 2, v_v_1236_);
lean_ctor_set(v___x_1242_, 1, v_k_1235_);
lean_ctor_set(v___x_1242_, 0, v___x_1303_);
v___x_1308_ = v___x_1242_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v_k_1235_);
lean_ctor_set(v_reuseFailAlloc_1309_, 2, v_v_1236_);
lean_ctor_set(v_reuseFailAlloc_1309_, 3, v___x_1306_);
lean_ctor_set(v_reuseFailAlloc_1309_, 4, v_r_1238_);
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
}
}
else
{
lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1370_; 
lean_inc(v_r_1238_);
lean_inc(v_v_1236_);
lean_inc(v_k_1235_);
lean_inc(v_size_1234_);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_r_1050_);
if (v_isSharedCheck_1370_ == 0)
{
lean_object* v_unused_1371_; lean_object* v_unused_1372_; lean_object* v_unused_1373_; lean_object* v_unused_1374_; lean_object* v_unused_1375_; 
v_unused_1371_ = lean_ctor_get(v_r_1050_, 4);
lean_dec(v_unused_1371_);
v_unused_1372_ = lean_ctor_get(v_r_1050_, 3);
lean_dec(v_unused_1372_);
v_unused_1373_ = lean_ctor_get(v_r_1050_, 2);
lean_dec(v_unused_1373_);
v_unused_1374_ = lean_ctor_get(v_r_1050_, 1);
lean_dec(v_unused_1374_);
v_unused_1375_ = lean_ctor_get(v_r_1050_, 0);
lean_dec(v_unused_1375_);
v___x_1318_ = v_r_1050_;
v_isShared_1319_ = v_isSharedCheck_1370_;
goto v_resetjp_1317_;
}
else
{
lean_dec(v_r_1050_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1370_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
if (lean_obj_tag(v_l_1237_) == 0)
{
if (lean_obj_tag(v_r_1238_) == 0)
{
lean_object* v_k_1320_; lean_object* v_v_1321_; lean_object* v_size_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
v_k_1320_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_k_1320_);
v_v_1321_ = lean_ctor_get(v___x_1244_, 1);
lean_inc(v_v_1321_);
lean_dec_ref(v___x_1244_);
v_size_1322_ = lean_ctor_get(v_l_1237_, 0);
v___x_1323_ = lean_nat_add(v___x_1239_, v_size_1234_);
lean_dec(v_size_1234_);
v___x_1324_ = lean_nat_add(v___x_1239_, v_size_1322_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 4, v_l_1237_);
lean_ctor_set(v___x_1318_, 3, v_tree_1245_);
lean_ctor_set(v___x_1318_, 2, v_v_1321_);
lean_ctor_set(v___x_1318_, 1, v_k_1320_);
lean_ctor_set(v___x_1318_, 0, v___x_1324_);
v___x_1326_ = v___x_1318_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_k_1320_);
lean_ctor_set(v_reuseFailAlloc_1330_, 2, v_v_1321_);
lean_ctor_set(v_reuseFailAlloc_1330_, 3, v_tree_1245_);
lean_ctor_set(v_reuseFailAlloc_1330_, 4, v_l_1237_);
v___x_1326_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1328_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 4, v_r_1238_);
lean_ctor_set(v___x_1242_, 3, v___x_1326_);
lean_ctor_set(v___x_1242_, 2, v_v_1236_);
lean_ctor_set(v___x_1242_, 1, v_k_1235_);
lean_ctor_set(v___x_1242_, 0, v___x_1323_);
v___x_1328_ = v___x_1242_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1323_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_k_1235_);
lean_ctor_set(v_reuseFailAlloc_1329_, 2, v_v_1236_);
lean_ctor_set(v_reuseFailAlloc_1329_, 3, v___x_1326_);
lean_ctor_set(v_reuseFailAlloc_1329_, 4, v_r_1238_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
else
{
lean_object* v_k_1331_; lean_object* v_v_1332_; lean_object* v_k_1333_; lean_object* v_v_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1348_; 
lean_dec(v_size_1234_);
v_k_1331_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_k_1331_);
v_v_1332_ = lean_ctor_get(v___x_1244_, 1);
lean_inc(v_v_1332_);
lean_dec_ref(v___x_1244_);
v_k_1333_ = lean_ctor_get(v_l_1237_, 1);
v_v_1334_ = lean_ctor_get(v_l_1237_, 2);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_l_1237_);
if (v_isSharedCheck_1348_ == 0)
{
lean_object* v_unused_1349_; lean_object* v_unused_1350_; lean_object* v_unused_1351_; 
v_unused_1349_ = lean_ctor_get(v_l_1237_, 4);
lean_dec(v_unused_1349_);
v_unused_1350_ = lean_ctor_get(v_l_1237_, 3);
lean_dec(v_unused_1350_);
v_unused_1351_ = lean_ctor_get(v_l_1237_, 0);
lean_dec(v_unused_1351_);
v___x_1336_ = v_l_1237_;
v_isShared_1337_ = v_isSharedCheck_1348_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_v_1334_);
lean_inc(v_k_1333_);
lean_dec(v_l_1237_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1348_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1338_ = lean_unsigned_to_nat(3u);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 4, v_r_1238_);
lean_ctor_set(v___x_1336_, 3, v_r_1238_);
lean_ctor_set(v___x_1336_, 2, v_v_1332_);
lean_ctor_set(v___x_1336_, 1, v_k_1331_);
lean_ctor_set(v___x_1336_, 0, v___x_1239_);
v___x_1340_ = v___x_1336_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_k_1331_);
lean_ctor_set(v_reuseFailAlloc_1347_, 2, v_v_1332_);
lean_ctor_set(v_reuseFailAlloc_1347_, 3, v_r_1238_);
lean_ctor_set(v_reuseFailAlloc_1347_, 4, v_r_1238_);
v___x_1340_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1342_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 3, v_r_1238_);
lean_ctor_set(v___x_1318_, 0, v___x_1239_);
v___x_1342_ = v___x_1318_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_k_1235_);
lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_v_1236_);
lean_ctor_set(v_reuseFailAlloc_1346_, 3, v_r_1238_);
lean_ctor_set(v_reuseFailAlloc_1346_, 4, v_r_1238_);
v___x_1342_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1344_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 4, v___x_1342_);
lean_ctor_set(v___x_1242_, 3, v___x_1340_);
lean_ctor_set(v___x_1242_, 2, v_v_1334_);
lean_ctor_set(v___x_1242_, 1, v_k_1333_);
lean_ctor_set(v___x_1242_, 0, v___x_1338_);
v___x_1344_ = v___x_1242_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1338_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_k_1333_);
lean_ctor_set(v_reuseFailAlloc_1345_, 2, v_v_1334_);
lean_ctor_set(v_reuseFailAlloc_1345_, 3, v___x_1340_);
lean_ctor_set(v_reuseFailAlloc_1345_, 4, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1238_) == 0)
{
lean_object* v_k_1352_; lean_object* v_v_1353_; lean_object* v___x_1354_; lean_object* v___x_1356_; 
lean_dec(v_size_1234_);
v_k_1352_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_k_1352_);
v_v_1353_ = lean_ctor_get(v___x_1244_, 1);
lean_inc(v_v_1353_);
lean_dec_ref(v___x_1244_);
v___x_1354_ = lean_unsigned_to_nat(3u);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 4, v_l_1237_);
lean_ctor_set(v___x_1318_, 2, v_v_1353_);
lean_ctor_set(v___x_1318_, 1, v_k_1352_);
lean_ctor_set(v___x_1318_, 0, v___x_1239_);
v___x_1356_ = v___x_1318_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_k_1352_);
lean_ctor_set(v_reuseFailAlloc_1360_, 2, v_v_1353_);
lean_ctor_set(v_reuseFailAlloc_1360_, 3, v_l_1237_);
lean_ctor_set(v_reuseFailAlloc_1360_, 4, v_l_1237_);
v___x_1356_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1358_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 4, v_r_1238_);
lean_ctor_set(v___x_1242_, 3, v___x_1356_);
lean_ctor_set(v___x_1242_, 2, v_v_1236_);
lean_ctor_set(v___x_1242_, 1, v_k_1235_);
lean_ctor_set(v___x_1242_, 0, v___x_1354_);
v___x_1358_ = v___x_1242_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_k_1235_);
lean_ctor_set(v_reuseFailAlloc_1359_, 2, v_v_1236_);
lean_ctor_set(v_reuseFailAlloc_1359_, 3, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1359_, 4, v_r_1238_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
else
{
lean_object* v_k_1361_; lean_object* v_v_1362_; lean_object* v___x_1364_; 
v_k_1361_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_k_1361_);
v_v_1362_ = lean_ctor_get(v___x_1244_, 1);
lean_inc(v_v_1362_);
lean_dec_ref(v___x_1244_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 3, v_r_1238_);
v___x_1364_ = v___x_1318_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_size_1234_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_k_1235_);
lean_ctor_set(v_reuseFailAlloc_1369_, 2, v_v_1236_);
lean_ctor_set(v_reuseFailAlloc_1369_, 3, v_r_1238_);
lean_ctor_set(v_reuseFailAlloc_1369_, 4, v_r_1238_);
v___x_1364_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1365_ = lean_unsigned_to_nat(2u);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 4, v___x_1364_);
lean_ctor_set(v___x_1242_, 3, v_r_1238_);
lean_ctor_set(v___x_1242_, 2, v_v_1362_);
lean_ctor_set(v___x_1242_, 1, v_k_1361_);
lean_ctor_set(v___x_1242_, 0, v___x_1365_);
v___x_1367_ = v___x_1242_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_k_1361_);
lean_ctor_set(v_reuseFailAlloc_1368_, 2, v_v_1362_);
lean_ctor_set(v_reuseFailAlloc_1368_, 3, v_r_1238_);
lean_ctor_set(v_reuseFailAlloc_1368_, 4, v___x_1364_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
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
lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1534_; 
lean_inc(v_r_1238_);
lean_inc(v_v_1236_);
lean_inc(v_k_1235_);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_r_1050_);
if (v_isSharedCheck_1534_ == 0)
{
lean_object* v_unused_1535_; lean_object* v_unused_1536_; lean_object* v_unused_1537_; lean_object* v_unused_1538_; lean_object* v_unused_1539_; 
v_unused_1535_ = lean_ctor_get(v_r_1050_, 4);
lean_dec(v_unused_1535_);
v_unused_1536_ = lean_ctor_get(v_r_1050_, 3);
lean_dec(v_unused_1536_);
v_unused_1537_ = lean_ctor_get(v_r_1050_, 2);
lean_dec(v_unused_1537_);
v_unused_1538_ = lean_ctor_get(v_r_1050_, 1);
lean_dec(v_unused_1538_);
v_unused_1539_ = lean_ctor_get(v_r_1050_, 0);
lean_dec(v_unused_1539_);
v___x_1383_ = v_r_1050_;
v_isShared_1384_ = v_isSharedCheck_1534_;
goto v_resetjp_1382_;
}
else
{
lean_dec(v_r_1050_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1534_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v_tree_1386_; 
v___x_1385_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1235_, v_v_1236_, v_l_1237_, v_r_1238_);
v_tree_1386_ = lean_ctor_get(v___x_1385_, 2);
lean_inc(v_tree_1386_);
if (lean_obj_tag(v_tree_1386_) == 0)
{
lean_object* v_k_1387_; lean_object* v_v_1388_; lean_object* v_size_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v_k_1387_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_k_1387_);
v_v_1388_ = lean_ctor_get(v___x_1385_, 1);
lean_inc(v_v_1388_);
lean_dec_ref(v___x_1385_);
v_size_1389_ = lean_ctor_get(v_tree_1386_, 0);
v___x_1390_ = lean_unsigned_to_nat(3u);
v___x_1391_ = lean_nat_mul(v___x_1390_, v_size_1389_);
v___x_1392_ = lean_nat_dec_lt(v___x_1391_, v_size_1229_);
lean_dec(v___x_1391_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
lean_dec(v_r_1233_);
v___x_1393_ = lean_nat_add(v___x_1239_, v_size_1229_);
v___x_1394_ = lean_nat_add(v___x_1393_, v_size_1389_);
lean_dec(v___x_1393_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v_tree_1386_);
lean_ctor_set(v___x_1383_, 3, v_l_1049_);
lean_ctor_set(v___x_1383_, 2, v_v_1388_);
lean_ctor_set(v___x_1383_, 1, v_k_1387_);
lean_ctor_set(v___x_1383_, 0, v___x_1394_);
v___x_1396_ = v___x_1383_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_k_1387_);
lean_ctor_set(v_reuseFailAlloc_1397_, 2, v_v_1388_);
lean_ctor_set(v_reuseFailAlloc_1397_, 3, v_l_1049_);
lean_ctor_set(v_reuseFailAlloc_1397_, 4, v_tree_1386_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
else
{
lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1463_; 
lean_inc(v_l_1232_);
lean_inc(v_v_1231_);
lean_inc(v_k_1230_);
lean_inc(v_size_1229_);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_l_1049_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; lean_object* v_unused_1465_; lean_object* v_unused_1466_; lean_object* v_unused_1467_; lean_object* v_unused_1468_; 
v_unused_1464_ = lean_ctor_get(v_l_1049_, 4);
lean_dec(v_unused_1464_);
v_unused_1465_ = lean_ctor_get(v_l_1049_, 3);
lean_dec(v_unused_1465_);
v_unused_1466_ = lean_ctor_get(v_l_1049_, 2);
lean_dec(v_unused_1466_);
v_unused_1467_ = lean_ctor_get(v_l_1049_, 1);
lean_dec(v_unused_1467_);
v_unused_1468_ = lean_ctor_get(v_l_1049_, 0);
lean_dec(v_unused_1468_);
v___x_1399_ = v_l_1049_;
v_isShared_1400_ = v_isSharedCheck_1463_;
goto v_resetjp_1398_;
}
else
{
lean_dec(v_l_1049_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1463_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v_size_1401_; lean_object* v_size_1402_; lean_object* v_k_1403_; lean_object* v_v_1404_; lean_object* v_l_1405_; lean_object* v_r_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v_size_1401_ = lean_ctor_get(v_l_1232_, 0);
v_size_1402_ = lean_ctor_get(v_r_1233_, 0);
v_k_1403_ = lean_ctor_get(v_r_1233_, 1);
v_v_1404_ = lean_ctor_get(v_r_1233_, 2);
v_l_1405_ = lean_ctor_get(v_r_1233_, 3);
v_r_1406_ = lean_ctor_get(v_r_1233_, 4);
v___x_1407_ = lean_unsigned_to_nat(2u);
v___x_1408_ = lean_nat_mul(v___x_1407_, v_size_1401_);
v___x_1409_ = lean_nat_dec_lt(v_size_1402_, v___x_1408_);
lean_dec(v___x_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1447_; 
lean_inc(v_r_1406_);
lean_inc(v_l_1405_);
lean_inc(v_v_1404_);
lean_inc(v_k_1403_);
lean_del_object(v___x_1399_);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_r_1233_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; lean_object* v_unused_1449_; lean_object* v_unused_1450_; lean_object* v_unused_1451_; lean_object* v_unused_1452_; 
v_unused_1448_ = lean_ctor_get(v_r_1233_, 4);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_r_1233_, 3);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_r_1233_, 2);
lean_dec(v_unused_1450_);
v_unused_1451_ = lean_ctor_get(v_r_1233_, 1);
lean_dec(v_unused_1451_);
v_unused_1452_ = lean_ctor_get(v_r_1233_, 0);
lean_dec(v_unused_1452_);
v___x_1411_ = v_r_1233_;
v_isShared_1412_ = v_isSharedCheck_1447_;
goto v_resetjp_1410_;
}
else
{
lean_dec(v_r_1233_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1447_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___x_1435_; lean_object* v___y_1437_; 
v___x_1413_ = lean_nat_add(v___x_1239_, v_size_1229_);
lean_dec(v_size_1229_);
v___x_1414_ = lean_nat_add(v___x_1413_, v_size_1389_);
lean_dec(v___x_1413_);
v___x_1435_ = lean_nat_add(v___x_1239_, v_size_1401_);
if (lean_obj_tag(v_l_1405_) == 0)
{
lean_object* v_size_1445_; 
v_size_1445_ = lean_ctor_get(v_l_1405_, 0);
lean_inc(v_size_1445_);
v___y_1437_ = v_size_1445_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1446_; 
v___x_1446_ = lean_unsigned_to_nat(0u);
v___y_1437_ = v___x_1446_;
goto v___jp_1436_;
}
v___jp_1415_:
{
lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1419_ = lean_nat_add(v___y_1417_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec(v___y_1417_);
lean_inc_ref(v_tree_1386_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 4, v_tree_1386_);
lean_ctor_set(v___x_1411_, 3, v_r_1406_);
lean_ctor_set(v___x_1411_, 2, v_v_1388_);
lean_ctor_set(v___x_1411_, 1, v_k_1387_);
lean_ctor_set(v___x_1411_, 0, v___x_1419_);
v___x_1421_ = v___x_1411_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1419_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_k_1387_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v_v_1388_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v_r_1406_);
lean_ctor_set(v_reuseFailAlloc_1434_, 4, v_tree_1386_);
v___x_1421_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
v_isSharedCheck_1428_ = !lean_is_exclusive(v_tree_1386_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; lean_object* v_unused_1430_; lean_object* v_unused_1431_; lean_object* v_unused_1432_; lean_object* v_unused_1433_; 
v_unused_1429_ = lean_ctor_get(v_tree_1386_, 4);
lean_dec(v_unused_1429_);
v_unused_1430_ = lean_ctor_get(v_tree_1386_, 3);
lean_dec(v_unused_1430_);
v_unused_1431_ = lean_ctor_get(v_tree_1386_, 2);
lean_dec(v_unused_1431_);
v_unused_1432_ = lean_ctor_get(v_tree_1386_, 1);
lean_dec(v_unused_1432_);
v_unused_1433_ = lean_ctor_get(v_tree_1386_, 0);
lean_dec(v_unused_1433_);
v___x_1423_ = v_tree_1386_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_dec(v_tree_1386_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 4, v___x_1421_);
lean_ctor_set(v___x_1423_, 3, v___y_1416_);
lean_ctor_set(v___x_1423_, 2, v_v_1404_);
lean_ctor_set(v___x_1423_, 1, v_k_1403_);
lean_ctor_set(v___x_1423_, 0, v___x_1414_);
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_k_1403_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v_v_1404_);
lean_ctor_set(v_reuseFailAlloc_1427_, 3, v___y_1416_);
lean_ctor_set(v_reuseFailAlloc_1427_, 4, v___x_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
v___jp_1436_:
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1438_ = lean_nat_add(v___x_1435_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec(v___x_1435_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v_l_1405_);
lean_ctor_set(v___x_1383_, 3, v_l_1232_);
lean_ctor_set(v___x_1383_, 2, v_v_1231_);
lean_ctor_set(v___x_1383_, 1, v_k_1230_);
lean_ctor_set(v___x_1383_, 0, v___x_1438_);
v___x_1440_ = v___x_1383_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_k_1230_);
lean_ctor_set(v_reuseFailAlloc_1444_, 2, v_v_1231_);
lean_ctor_set(v_reuseFailAlloc_1444_, 3, v_l_1232_);
lean_ctor_set(v_reuseFailAlloc_1444_, 4, v_l_1405_);
v___x_1440_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_nat_add(v___x_1239_, v_size_1389_);
if (lean_obj_tag(v_r_1406_) == 0)
{
lean_object* v_size_1442_; 
v_size_1442_ = lean_ctor_get(v_r_1406_, 0);
lean_inc(v_size_1442_);
v___y_1416_ = v___x_1440_;
v___y_1417_ = v___x_1441_;
v___y_1418_ = v_size_1442_;
goto v___jp_1415_;
}
else
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_unsigned_to_nat(0u);
v___y_1416_ = v___x_1440_;
v___y_1417_ = v___x_1441_;
v___y_1418_ = v___x_1443_;
goto v___jp_1415_;
}
}
}
}
}
else
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1453_ = lean_nat_add(v___x_1239_, v_size_1229_);
lean_dec(v_size_1229_);
v___x_1454_ = lean_nat_add(v___x_1453_, v_size_1389_);
lean_dec(v___x_1453_);
v___x_1455_ = lean_nat_add(v___x_1239_, v_size_1389_);
v___x_1456_ = lean_nat_add(v___x_1455_, v_size_1402_);
lean_dec(v___x_1455_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v_tree_1386_);
lean_ctor_set(v___x_1383_, 3, v_r_1233_);
lean_ctor_set(v___x_1383_, 2, v_v_1388_);
lean_ctor_set(v___x_1383_, 1, v_k_1387_);
lean_ctor_set(v___x_1383_, 0, v___x_1456_);
v___x_1458_ = v___x_1383_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_k_1387_);
lean_ctor_set(v_reuseFailAlloc_1462_, 2, v_v_1388_);
lean_ctor_set(v_reuseFailAlloc_1462_, 3, v_r_1233_);
lean_ctor_set(v_reuseFailAlloc_1462_, 4, v_tree_1386_);
v___x_1458_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___x_1460_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 4, v___x_1458_);
lean_ctor_set(v___x_1399_, 0, v___x_1454_);
v___x_1460_ = v___x_1399_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1454_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_k_1230_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_v_1231_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v_l_1232_);
lean_ctor_set(v_reuseFailAlloc_1461_, 4, v___x_1458_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1232_) == 0)
{
lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1492_; 
lean_inc_ref(v_l_1232_);
lean_inc(v_v_1231_);
lean_inc(v_k_1230_);
lean_inc(v_size_1229_);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_l_1049_);
if (v_isSharedCheck_1492_ == 0)
{
lean_object* v_unused_1493_; lean_object* v_unused_1494_; lean_object* v_unused_1495_; lean_object* v_unused_1496_; lean_object* v_unused_1497_; 
v_unused_1493_ = lean_ctor_get(v_l_1049_, 4);
lean_dec(v_unused_1493_);
v_unused_1494_ = lean_ctor_get(v_l_1049_, 3);
lean_dec(v_unused_1494_);
v_unused_1495_ = lean_ctor_get(v_l_1049_, 2);
lean_dec(v_unused_1495_);
v_unused_1496_ = lean_ctor_get(v_l_1049_, 1);
lean_dec(v_unused_1496_);
v_unused_1497_ = lean_ctor_get(v_l_1049_, 0);
lean_dec(v_unused_1497_);
v___x_1470_ = v_l_1049_;
v_isShared_1471_ = v_isSharedCheck_1492_;
goto v_resetjp_1469_;
}
else
{
lean_dec(v_l_1049_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1492_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
if (lean_obj_tag(v_r_1233_) == 0)
{
lean_object* v_k_1472_; lean_object* v_v_1473_; lean_object* v_size_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1478_; 
v_k_1472_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_k_1472_);
v_v_1473_ = lean_ctor_get(v___x_1385_, 1);
lean_inc(v_v_1473_);
lean_dec_ref(v___x_1385_);
v_size_1474_ = lean_ctor_get(v_r_1233_, 0);
v___x_1475_ = lean_nat_add(v___x_1239_, v_size_1229_);
lean_dec(v_size_1229_);
v___x_1476_ = lean_nat_add(v___x_1239_, v_size_1474_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v_tree_1386_);
lean_ctor_set(v___x_1383_, 3, v_r_1233_);
lean_ctor_set(v___x_1383_, 2, v_v_1473_);
lean_ctor_set(v___x_1383_, 1, v_k_1472_);
lean_ctor_set(v___x_1383_, 0, v___x_1476_);
v___x_1478_ = v___x_1383_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_k_1472_);
lean_ctor_set(v_reuseFailAlloc_1482_, 2, v_v_1473_);
lean_ctor_set(v_reuseFailAlloc_1482_, 3, v_r_1233_);
lean_ctor_set(v_reuseFailAlloc_1482_, 4, v_tree_1386_);
v___x_1478_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
lean_object* v___x_1480_; 
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 4, v___x_1478_);
lean_ctor_set(v___x_1470_, 0, v___x_1475_);
v___x_1480_ = v___x_1470_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_k_1230_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_v_1231_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v_l_1232_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
else
{
lean_object* v_k_1483_; lean_object* v_v_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; 
lean_dec(v_size_1229_);
v_k_1483_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_k_1483_);
v_v_1484_ = lean_ctor_get(v___x_1385_, 1);
lean_inc(v_v_1484_);
lean_dec_ref(v___x_1385_);
v___x_1485_ = lean_unsigned_to_nat(3u);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v_r_1233_);
lean_ctor_set(v___x_1383_, 3, v_r_1233_);
lean_ctor_set(v___x_1383_, 2, v_v_1484_);
lean_ctor_set(v___x_1383_, 1, v_k_1483_);
lean_ctor_set(v___x_1383_, 0, v___x_1239_);
v___x_1487_ = v___x_1383_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_k_1483_);
lean_ctor_set(v_reuseFailAlloc_1491_, 2, v_v_1484_);
lean_ctor_set(v_reuseFailAlloc_1491_, 3, v_r_1233_);
lean_ctor_set(v_reuseFailAlloc_1491_, 4, v_r_1233_);
v___x_1487_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1489_; 
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 4, v___x_1487_);
lean_ctor_set(v___x_1470_, 0, v___x_1485_);
v___x_1489_ = v___x_1470_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_k_1230_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_v_1231_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_l_1232_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v___x_1487_);
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
else
{
if (lean_obj_tag(v_r_1233_) == 0)
{
lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1522_; 
lean_inc(v_l_1232_);
lean_inc(v_v_1231_);
lean_inc(v_k_1230_);
v_isSharedCheck_1522_ = !lean_is_exclusive(v_l_1049_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; lean_object* v_unused_1524_; lean_object* v_unused_1525_; lean_object* v_unused_1526_; lean_object* v_unused_1527_; 
v_unused_1523_ = lean_ctor_get(v_l_1049_, 4);
lean_dec(v_unused_1523_);
v_unused_1524_ = lean_ctor_get(v_l_1049_, 3);
lean_dec(v_unused_1524_);
v_unused_1525_ = lean_ctor_get(v_l_1049_, 2);
lean_dec(v_unused_1525_);
v_unused_1526_ = lean_ctor_get(v_l_1049_, 1);
lean_dec(v_unused_1526_);
v_unused_1527_ = lean_ctor_get(v_l_1049_, 0);
lean_dec(v_unused_1527_);
v___x_1499_ = v_l_1049_;
v_isShared_1500_ = v_isSharedCheck_1522_;
goto v_resetjp_1498_;
}
else
{
lean_dec(v_l_1049_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1522_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v_k_1501_; lean_object* v_v_1502_; lean_object* v_k_1503_; lean_object* v_v_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1518_; 
v_k_1501_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_k_1501_);
v_v_1502_ = lean_ctor_get(v___x_1385_, 1);
lean_inc(v_v_1502_);
lean_dec_ref(v___x_1385_);
v_k_1503_ = lean_ctor_get(v_r_1233_, 1);
v_v_1504_ = lean_ctor_get(v_r_1233_, 2);
v_isSharedCheck_1518_ = !lean_is_exclusive(v_r_1233_);
if (v_isSharedCheck_1518_ == 0)
{
lean_object* v_unused_1519_; lean_object* v_unused_1520_; lean_object* v_unused_1521_; 
v_unused_1519_ = lean_ctor_get(v_r_1233_, 4);
lean_dec(v_unused_1519_);
v_unused_1520_ = lean_ctor_get(v_r_1233_, 3);
lean_dec(v_unused_1520_);
v_unused_1521_ = lean_ctor_get(v_r_1233_, 0);
lean_dec(v_unused_1521_);
v___x_1506_ = v_r_1233_;
v_isShared_1507_ = v_isSharedCheck_1518_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_v_1504_);
lean_inc(v_k_1503_);
lean_dec(v_r_1233_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1518_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1508_ = lean_unsigned_to_nat(3u);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 4, v_l_1232_);
lean_ctor_set(v___x_1506_, 3, v_l_1232_);
lean_ctor_set(v___x_1506_, 2, v_v_1231_);
lean_ctor_set(v___x_1506_, 1, v_k_1230_);
lean_ctor_set(v___x_1506_, 0, v___x_1239_);
v___x_1510_ = v___x_1506_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_k_1230_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_v_1231_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v_l_1232_);
lean_ctor_set(v_reuseFailAlloc_1517_, 4, v_l_1232_);
v___x_1510_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1512_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v_l_1232_);
lean_ctor_set(v___x_1383_, 3, v_l_1232_);
lean_ctor_set(v___x_1383_, 2, v_v_1502_);
lean_ctor_set(v___x_1383_, 1, v_k_1501_);
lean_ctor_set(v___x_1383_, 0, v___x_1239_);
v___x_1512_ = v___x_1383_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_k_1501_);
lean_ctor_set(v_reuseFailAlloc_1516_, 2, v_v_1502_);
lean_ctor_set(v_reuseFailAlloc_1516_, 3, v_l_1232_);
lean_ctor_set(v_reuseFailAlloc_1516_, 4, v_l_1232_);
v___x_1512_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1514_; 
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 4, v___x_1512_);
lean_ctor_set(v___x_1499_, 3, v___x_1510_);
lean_ctor_set(v___x_1499_, 2, v_v_1504_);
lean_ctor_set(v___x_1499_, 1, v_k_1503_);
lean_ctor_set(v___x_1499_, 0, v___x_1508_);
v___x_1514_ = v___x_1499_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1508_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v_k_1503_);
lean_ctor_set(v_reuseFailAlloc_1515_, 2, v_v_1504_);
lean_ctor_set(v_reuseFailAlloc_1515_, 3, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1515_, 4, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
}
else
{
lean_object* v_k_1528_; lean_object* v_v_1529_; lean_object* v___x_1530_; lean_object* v___x_1532_; 
v_k_1528_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_k_1528_);
v_v_1529_ = lean_ctor_get(v___x_1385_, 1);
lean_inc(v_v_1529_);
lean_dec_ref(v___x_1385_);
v___x_1530_ = lean_unsigned_to_nat(2u);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v_r_1233_);
lean_ctor_set(v___x_1383_, 3, v_l_1049_);
lean_ctor_set(v___x_1383_, 2, v_v_1529_);
lean_ctor_set(v___x_1383_, 1, v_k_1528_);
lean_ctor_set(v___x_1383_, 0, v___x_1530_);
v___x_1532_ = v___x_1383_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1530_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_k_1528_);
lean_ctor_set(v_reuseFailAlloc_1533_, 2, v_v_1529_);
lean_ctor_set(v_reuseFailAlloc_1533_, 3, v_l_1049_);
lean_ctor_set(v_reuseFailAlloc_1533_, 4, v_r_1233_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
}
}
}
else
{
return v_l_1049_;
}
}
else
{
return v_r_1050_;
}
}
default: 
{
lean_object* v_impl_1540_; lean_object* v___x_1541_; 
v_impl_1540_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1045_, v_r_1050_);
v___x_1541_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1540_) == 0)
{
if (lean_obj_tag(v_l_1049_) == 0)
{
lean_object* v_size_1542_; lean_object* v_size_1543_; lean_object* v_k_1544_; lean_object* v_v_1545_; lean_object* v_l_1546_; lean_object* v_r_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v_size_1542_ = lean_ctor_get(v_impl_1540_, 0);
lean_inc(v_size_1542_);
v_size_1543_ = lean_ctor_get(v_l_1049_, 0);
v_k_1544_ = lean_ctor_get(v_l_1049_, 1);
v_v_1545_ = lean_ctor_get(v_l_1049_, 2);
v_l_1546_ = lean_ctor_get(v_l_1049_, 3);
v_r_1547_ = lean_ctor_get(v_l_1049_, 4);
lean_inc(v_r_1547_);
v___x_1548_ = lean_unsigned_to_nat(3u);
v___x_1549_ = lean_nat_mul(v___x_1548_, v_size_1542_);
v___x_1550_ = lean_nat_dec_lt(v___x_1549_, v_size_1543_);
lean_dec(v___x_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; 
lean_dec(v_r_1547_);
v___x_1551_ = lean_nat_add(v___x_1541_, v_size_1543_);
v___x_1552_ = lean_nat_add(v___x_1551_, v_size_1542_);
lean_dec(v_size_1542_);
lean_dec(v___x_1551_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 4, v_impl_1540_);
lean_ctor_set(v___x_1052_, 0, v___x_1552_);
v___x_1554_ = v___x_1052_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_k_1047_);
lean_ctor_set(v_reuseFailAlloc_1555_, 2, v_v_1048_);
lean_ctor_set(v_reuseFailAlloc_1555_, 3, v_l_1049_);
lean_ctor_set(v_reuseFailAlloc_1555_, 4, v_impl_1540_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
else
{
lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1621_; 
lean_inc(v_l_1546_);
lean_inc(v_v_1545_);
lean_inc(v_k_1544_);
lean_inc(v_size_1543_);
v_isSharedCheck_1621_ = !lean_is_exclusive(v_l_1049_);
if (v_isSharedCheck_1621_ == 0)
{
lean_object* v_unused_1622_; lean_object* v_unused_1623_; lean_object* v_unused_1624_; lean_object* v_unused_1625_; lean_object* v_unused_1626_; 
v_unused_1622_ = lean_ctor_get(v_l_1049_, 4);
lean_dec(v_unused_1622_);
v_unused_1623_ = lean_ctor_get(v_l_1049_, 3);
lean_dec(v_unused_1623_);
v_unused_1624_ = lean_ctor_get(v_l_1049_, 2);
lean_dec(v_unused_1624_);
v_unused_1625_ = lean_ctor_get(v_l_1049_, 1);
lean_dec(v_unused_1625_);
v_unused_1626_ = lean_ctor_get(v_l_1049_, 0);
lean_dec(v_unused_1626_);
v___x_1557_ = v_l_1049_;
v_isShared_1558_ = v_isSharedCheck_1621_;
goto v_resetjp_1556_;
}
else
{
lean_dec(v_l_1049_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1621_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v_size_1559_; lean_object* v_size_1560_; lean_object* v_k_1561_; lean_object* v_v_1562_; lean_object* v_l_1563_; lean_object* v_r_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; 
v_size_1559_ = lean_ctor_get(v_l_1546_, 0);
v_size_1560_ = lean_ctor_get(v_r_1547_, 0);
v_k_1561_ = lean_ctor_get(v_r_1547_, 1);
v_v_1562_ = lean_ctor_get(v_r_1547_, 2);
v_l_1563_ = lean_ctor_get(v_r_1547_, 3);
v_r_1564_ = lean_ctor_get(v_r_1547_, 4);
v___x_1565_ = lean_unsigned_to_nat(2u);
v___x_1566_ = lean_nat_mul(v___x_1565_, v_size_1559_);
v___x_1567_ = lean_nat_dec_lt(v_size_1560_, v___x_1566_);
lean_dec(v___x_1566_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1596_; 
lean_inc(v_r_1564_);
lean_inc(v_l_1563_);
lean_inc(v_v_1562_);
lean_inc(v_k_1561_);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_r_1547_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; lean_object* v_unused_1598_; lean_object* v_unused_1599_; lean_object* v_unused_1600_; lean_object* v_unused_1601_; 
v_unused_1597_ = lean_ctor_get(v_r_1547_, 4);
lean_dec(v_unused_1597_);
v_unused_1598_ = lean_ctor_get(v_r_1547_, 3);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_r_1547_, 2);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v_r_1547_, 1);
lean_dec(v_unused_1600_);
v_unused_1601_ = lean_ctor_get(v_r_1547_, 0);
lean_dec(v_unused_1601_);
v___x_1569_ = v_r_1547_;
v_isShared_1570_ = v_isSharedCheck_1596_;
goto v_resetjp_1568_;
}
else
{
lean_dec(v_r_1547_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1596_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___x_1584_; lean_object* v___y_1586_; 
v___x_1571_ = lean_nat_add(v___x_1541_, v_size_1543_);
lean_dec(v_size_1543_);
v___x_1572_ = lean_nat_add(v___x_1571_, v_size_1542_);
lean_dec(v___x_1571_);
v___x_1584_ = lean_nat_add(v___x_1541_, v_size_1559_);
if (lean_obj_tag(v_l_1563_) == 0)
{
lean_object* v_size_1594_; 
v_size_1594_ = lean_ctor_get(v_l_1563_, 0);
lean_inc(v_size_1594_);
v___y_1586_ = v_size_1594_;
goto v___jp_1585_;
}
else
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_unsigned_to_nat(0u);
v___y_1586_ = v___x_1595_;
goto v___jp_1585_;
}
v___jp_1573_:
{
lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1577_ = lean_nat_add(v___y_1574_, v___y_1576_);
lean_dec(v___y_1576_);
lean_dec(v___y_1574_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 4, v_impl_1540_);
lean_ctor_set(v___x_1569_, 3, v_r_1564_);
lean_ctor_set(v___x_1569_, 2, v_v_1048_);
lean_ctor_set(v___x_1569_, 1, v_k_1047_);
lean_ctor_set(v___x_1569_, 0, v___x_1577_);
v___x_1579_ = v___x_1569_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_k_1047_);
lean_ctor_set(v_reuseFailAlloc_1583_, 2, v_v_1048_);
lean_ctor_set(v_reuseFailAlloc_1583_, 3, v_r_1564_);
lean_ctor_set(v_reuseFailAlloc_1583_, 4, v_impl_1540_);
v___x_1579_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1581_; 
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 4, v___x_1579_);
lean_ctor_set(v___x_1557_, 3, v___y_1575_);
lean_ctor_set(v___x_1557_, 2, v_v_1562_);
lean_ctor_set(v___x_1557_, 1, v_k_1561_);
lean_ctor_set(v___x_1557_, 0, v___x_1572_);
v___x_1581_ = v___x_1557_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_k_1561_);
lean_ctor_set(v_reuseFailAlloc_1582_, 2, v_v_1562_);
lean_ctor_set(v_reuseFailAlloc_1582_, 3, v___y_1575_);
lean_ctor_set(v_reuseFailAlloc_1582_, 4, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
v___jp_1585_:
{
lean_object* v___x_1587_; lean_object* v___x_1589_; 
v___x_1587_ = lean_nat_add(v___x_1584_, v___y_1586_);
lean_dec(v___y_1586_);
lean_dec(v___x_1584_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 4, v_l_1563_);
lean_ctor_set(v___x_1052_, 3, v_l_1546_);
lean_ctor_set(v___x_1052_, 2, v_v_1545_);
lean_ctor_set(v___x_1052_, 1, v_k_1544_);
lean_ctor_set(v___x_1052_, 0, v___x_1587_);
v___x_1589_ = v___x_1052_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_k_1544_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_v_1545_);
lean_ctor_set(v_reuseFailAlloc_1593_, 3, v_l_1546_);
lean_ctor_set(v_reuseFailAlloc_1593_, 4, v_l_1563_);
v___x_1589_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1590_; 
v___x_1590_ = lean_nat_add(v___x_1541_, v_size_1542_);
lean_dec(v_size_1542_);
if (lean_obj_tag(v_r_1564_) == 0)
{
lean_object* v_size_1591_; 
v_size_1591_ = lean_ctor_get(v_r_1564_, 0);
lean_inc(v_size_1591_);
v___y_1574_ = v___x_1590_;
v___y_1575_ = v___x_1589_;
v___y_1576_ = v_size_1591_;
goto v___jp_1573_;
}
else
{
lean_object* v___x_1592_; 
v___x_1592_ = lean_unsigned_to_nat(0u);
v___y_1574_ = v___x_1590_;
v___y_1575_ = v___x_1589_;
v___y_1576_ = v___x_1592_;
goto v___jp_1573_;
}
}
}
}
}
else
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1607_; 
lean_del_object(v___x_1052_);
v___x_1602_ = lean_nat_add(v___x_1541_, v_size_1543_);
lean_dec(v_size_1543_);
v___x_1603_ = lean_nat_add(v___x_1602_, v_size_1542_);
lean_dec(v___x_1602_);
v___x_1604_ = lean_nat_add(v___x_1541_, v_size_1542_);
lean_dec(v_size_1542_);
v___x_1605_ = lean_nat_add(v___x_1604_, v_size_1560_);
lean_dec(v___x_1604_);
lean_inc_ref(v_impl_1540_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 4, v_impl_1540_);
lean_ctor_set(v___x_1557_, 3, v_r_1547_);
lean_ctor_set(v___x_1557_, 2, v_v_1048_);
lean_ctor_set(v___x_1557_, 1, v_k_1047_);
lean_ctor_set(v___x_1557_, 0, v___x_1605_);
v___x_1607_ = v___x_1557_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_k_1047_);
lean_ctor_set(v_reuseFailAlloc_1620_, 2, v_v_1048_);
lean_ctor_set(v_reuseFailAlloc_1620_, 3, v_r_1547_);
lean_ctor_set(v_reuseFailAlloc_1620_, 4, v_impl_1540_);
v___x_1607_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
v_isSharedCheck_1614_ = !lean_is_exclusive(v_impl_1540_);
if (v_isSharedCheck_1614_ == 0)
{
lean_object* v_unused_1615_; lean_object* v_unused_1616_; lean_object* v_unused_1617_; lean_object* v_unused_1618_; lean_object* v_unused_1619_; 
v_unused_1615_ = lean_ctor_get(v_impl_1540_, 4);
lean_dec(v_unused_1615_);
v_unused_1616_ = lean_ctor_get(v_impl_1540_, 3);
lean_dec(v_unused_1616_);
v_unused_1617_ = lean_ctor_get(v_impl_1540_, 2);
lean_dec(v_unused_1617_);
v_unused_1618_ = lean_ctor_get(v_impl_1540_, 1);
lean_dec(v_unused_1618_);
v_unused_1619_ = lean_ctor_get(v_impl_1540_, 0);
lean_dec(v_unused_1619_);
v___x_1609_ = v_impl_1540_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_dec(v_impl_1540_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 4, v___x_1607_);
lean_ctor_set(v___x_1609_, 3, v_l_1546_);
lean_ctor_set(v___x_1609_, 2, v_v_1545_);
lean_ctor_set(v___x_1609_, 1, v_k_1544_);
lean_ctor_set(v___x_1609_, 0, v___x_1603_);
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_k_1544_);
lean_ctor_set(v_reuseFailAlloc_1613_, 2, v_v_1545_);
lean_ctor_set(v_reuseFailAlloc_1613_, 3, v_l_1546_);
lean_ctor_set(v_reuseFailAlloc_1613_, 4, v___x_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1627_; lean_object* v___x_1628_; lean_object* v___x_1630_; 
v_size_1627_ = lean_ctor_get(v_impl_1540_, 0);
lean_inc(v_size_1627_);
v___x_1628_ = lean_nat_add(v___x_1541_, v_size_1627_);
lean_dec(v_size_1627_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 4, v_impl_1540_);
lean_ctor_set(v___x_1052_, 0, v___x_1628_);
v___x_1630_ = v___x_1052_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_k_1047_);
lean_ctor_set(v_reuseFailAlloc_1631_, 2, v_v_1048_);
lean_ctor_set(v_reuseFailAlloc_1631_, 3, v_l_1049_);
lean_ctor_set(v_reuseFailAlloc_1631_, 4, v_impl_1540_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
else
{
if (lean_obj_tag(v_l_1049_) == 0)
{
lean_object* v_l_1632_; 
v_l_1632_ = lean_ctor_get(v_l_1049_, 3);
if (lean_obj_tag(v_l_1632_) == 0)
{
lean_object* v_r_1633_; 
lean_inc_ref(v_l_1632_);
v_r_1633_ = lean_ctor_get(v_l_1049_, 4);
lean_inc(v_r_1633_);
if (lean_obj_tag(v_r_1633_) == 0)
{
lean_object* v_size_1634_; lean_object* v_k_1635_; lean_object* v_v_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1649_; 
v_size_1634_ = lean_ctor_get(v_l_1049_, 0);
v_k_1635_ = lean_ctor_get(v_l_1049_, 1);
v_v_1636_ = lean_ctor_get(v_l_1049_, 2);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_l_1049_);
if (v_isSharedCheck_1649_ == 0)
{
lean_object* v_unused_1650_; lean_object* v_unused_1651_; 
v_unused_1650_ = lean_ctor_get(v_l_1049_, 4);
lean_dec(v_unused_1650_);
v_unused_1651_ = lean_ctor_get(v_l_1049_, 3);
lean_dec(v_unused_1651_);
v___x_1638_ = v_l_1049_;
v_isShared_1639_ = v_isSharedCheck_1649_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_v_1636_);
lean_inc(v_k_1635_);
lean_inc(v_size_1634_);
lean_dec(v_l_1049_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1649_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v_size_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1644_; 
v_size_1640_ = lean_ctor_get(v_r_1633_, 0);
v___x_1641_ = lean_nat_add(v___x_1541_, v_size_1634_);
lean_dec(v_size_1634_);
v___x_1642_ = lean_nat_add(v___x_1541_, v_size_1640_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 4, v_impl_1540_);
lean_ctor_set(v___x_1638_, 3, v_r_1633_);
lean_ctor_set(v___x_1638_, 2, v_v_1048_);
lean_ctor_set(v___x_1638_, 1, v_k_1047_);
lean_ctor_set(v___x_1638_, 0, v___x_1642_);
v___x_1644_ = v___x_1638_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1642_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_k_1047_);
lean_ctor_set(v_reuseFailAlloc_1648_, 2, v_v_1048_);
lean_ctor_set(v_reuseFailAlloc_1648_, 3, v_r_1633_);
lean_ctor_set(v_reuseFailAlloc_1648_, 4, v_impl_1540_);
v___x_1644_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1646_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 4, v___x_1644_);
lean_ctor_set(v___x_1052_, 3, v_l_1632_);
lean_ctor_set(v___x_1052_, 2, v_v_1636_);
lean_ctor_set(v___x_1052_, 1, v_k_1635_);
lean_ctor_set(v___x_1052_, 0, v___x_1641_);
v___x_1646_ = v___x_1052_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_k_1635_);
lean_ctor_set(v_reuseFailAlloc_1647_, 2, v_v_1636_);
lean_ctor_set(v_reuseFailAlloc_1647_, 3, v_l_1632_);
lean_ctor_set(v_reuseFailAlloc_1647_, 4, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
else
{
lean_object* v_k_1652_; lean_object* v_v_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1664_; 
v_k_1652_ = lean_ctor_get(v_l_1049_, 1);
v_v_1653_ = lean_ctor_get(v_l_1049_, 2);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_l_1049_);
if (v_isSharedCheck_1664_ == 0)
{
lean_object* v_unused_1665_; lean_object* v_unused_1666_; lean_object* v_unused_1667_; 
v_unused_1665_ = lean_ctor_get(v_l_1049_, 4);
lean_dec(v_unused_1665_);
v_unused_1666_ = lean_ctor_get(v_l_1049_, 3);
lean_dec(v_unused_1666_);
v_unused_1667_ = lean_ctor_get(v_l_1049_, 0);
lean_dec(v_unused_1667_);
v___x_1655_ = v_l_1049_;
v_isShared_1656_ = v_isSharedCheck_1664_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_v_1653_);
lean_inc(v_k_1652_);
lean_dec(v_l_1049_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1664_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1657_ = lean_unsigned_to_nat(3u);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 3, v_r_1633_);
lean_ctor_set(v___x_1655_, 2, v_v_1048_);
lean_ctor_set(v___x_1655_, 1, v_k_1047_);
lean_ctor_set(v___x_1655_, 0, v___x_1541_);
v___x_1659_ = v___x_1655_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_k_1047_);
lean_ctor_set(v_reuseFailAlloc_1663_, 2, v_v_1048_);
lean_ctor_set(v_reuseFailAlloc_1663_, 3, v_r_1633_);
lean_ctor_set(v_reuseFailAlloc_1663_, 4, v_r_1633_);
v___x_1659_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1661_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 4, v___x_1659_);
lean_ctor_set(v___x_1052_, 3, v_l_1632_);
lean_ctor_set(v___x_1052_, 2, v_v_1653_);
lean_ctor_set(v___x_1052_, 1, v_k_1652_);
lean_ctor_set(v___x_1052_, 0, v___x_1657_);
v___x_1661_ = v___x_1052_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_k_1652_);
lean_ctor_set(v_reuseFailAlloc_1662_, 2, v_v_1653_);
lean_ctor_set(v_reuseFailAlloc_1662_, 3, v_l_1632_);
lean_ctor_set(v_reuseFailAlloc_1662_, 4, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
else
{
lean_object* v_r_1668_; 
v_r_1668_ = lean_ctor_get(v_l_1049_, 4);
lean_inc(v_r_1668_);
if (lean_obj_tag(v_r_1668_) == 0)
{
lean_object* v_k_1669_; lean_object* v_v_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1693_; 
lean_inc(v_l_1632_);
v_k_1669_ = lean_ctor_get(v_l_1049_, 1);
v_v_1670_ = lean_ctor_get(v_l_1049_, 2);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_l_1049_);
if (v_isSharedCheck_1693_ == 0)
{
lean_object* v_unused_1694_; lean_object* v_unused_1695_; lean_object* v_unused_1696_; 
v_unused_1694_ = lean_ctor_get(v_l_1049_, 4);
lean_dec(v_unused_1694_);
v_unused_1695_ = lean_ctor_get(v_l_1049_, 3);
lean_dec(v_unused_1695_);
v_unused_1696_ = lean_ctor_get(v_l_1049_, 0);
lean_dec(v_unused_1696_);
v___x_1672_ = v_l_1049_;
v_isShared_1673_ = v_isSharedCheck_1693_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_v_1670_);
lean_inc(v_k_1669_);
lean_dec(v_l_1049_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1693_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v_k_1674_; lean_object* v_v_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1689_; 
v_k_1674_ = lean_ctor_get(v_r_1668_, 1);
v_v_1675_ = lean_ctor_get(v_r_1668_, 2);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_r_1668_);
if (v_isSharedCheck_1689_ == 0)
{
lean_object* v_unused_1690_; lean_object* v_unused_1691_; lean_object* v_unused_1692_; 
v_unused_1690_ = lean_ctor_get(v_r_1668_, 4);
lean_dec(v_unused_1690_);
v_unused_1691_ = lean_ctor_get(v_r_1668_, 3);
lean_dec(v_unused_1691_);
v_unused_1692_ = lean_ctor_get(v_r_1668_, 0);
lean_dec(v_unused_1692_);
v___x_1677_ = v_r_1668_;
v_isShared_1678_ = v_isSharedCheck_1689_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_v_1675_);
lean_inc(v_k_1674_);
lean_dec(v_r_1668_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1689_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = lean_unsigned_to_nat(3u);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 4, v_l_1632_);
lean_ctor_set(v___x_1677_, 3, v_l_1632_);
lean_ctor_set(v___x_1677_, 2, v_v_1670_);
lean_ctor_set(v___x_1677_, 1, v_k_1669_);
lean_ctor_set(v___x_1677_, 0, v___x_1541_);
v___x_1681_ = v___x_1677_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_k_1669_);
lean_ctor_set(v_reuseFailAlloc_1688_, 2, v_v_1670_);
lean_ctor_set(v_reuseFailAlloc_1688_, 3, v_l_1632_);
lean_ctor_set(v_reuseFailAlloc_1688_, 4, v_l_1632_);
v___x_1681_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1683_; 
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 4, v_l_1632_);
lean_ctor_set(v___x_1672_, 2, v_v_1048_);
lean_ctor_set(v___x_1672_, 1, v_k_1047_);
lean_ctor_set(v___x_1672_, 0, v___x_1541_);
v___x_1683_ = v___x_1672_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_k_1047_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_v_1048_);
lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_l_1632_);
lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_l_1632_);
v___x_1683_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1685_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 4, v___x_1683_);
lean_ctor_set(v___x_1052_, 3, v___x_1681_);
lean_ctor_set(v___x_1052_, 2, v_v_1675_);
lean_ctor_set(v___x_1052_, 1, v_k_1674_);
lean_ctor_set(v___x_1052_, 0, v___x_1679_);
v___x_1685_ = v___x_1052_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_k_1674_);
lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_v_1675_);
lean_ctor_set(v_reuseFailAlloc_1686_, 3, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1686_, 4, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
}
}
else
{
lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___x_1697_ = lean_unsigned_to_nat(2u);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 4, v_r_1668_);
lean_ctor_set(v___x_1052_, 0, v___x_1697_);
v___x_1699_ = v___x_1052_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1697_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_k_1047_);
lean_ctor_set(v_reuseFailAlloc_1700_, 2, v_v_1048_);
lean_ctor_set(v_reuseFailAlloc_1700_, 3, v_l_1049_);
lean_ctor_set(v_reuseFailAlloc_1700_, 4, v_r_1668_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
else
{
lean_object* v___x_1702_; 
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 4, v_l_1049_);
lean_ctor_set(v___x_1052_, 0, v___x_1541_);
v___x_1702_ = v___x_1052_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_k_1047_);
lean_ctor_set(v_reuseFailAlloc_1703_, 2, v_v_1048_);
lean_ctor_set(v_reuseFailAlloc_1703_, 3, v_l_1049_);
lean_ctor_set(v_reuseFailAlloc_1703_, 4, v_l_1049_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
}
}
else
{
return v_t_1046_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object* v_k_1706_, lean_object* v_t_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1706_, v_t_1707_);
lean_dec(v_k_1706_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object* v_ext_1709_, lean_object* v_declName_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v___x_1714_; lean_object* v_ext_1715_; lean_object* v_toEnvExtension_1716_; lean_object* v_env_1717_; lean_object* v_asyncMode_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___y_1722_; lean_object* v_funCC_1748_; uint8_t v___x_1749_; 
v___x_1714_ = lean_st_ref_get(v_a_1712_);
v_ext_1715_ = lean_ctor_get(v_ext_1709_, 1);
v_toEnvExtension_1716_ = lean_ctor_get(v_ext_1715_, 0);
v_env_1717_ = lean_ctor_get(v___x_1714_, 0);
lean_inc_ref(v_env_1717_);
lean_dec(v___x_1714_);
v_asyncMode_1718_ = lean_ctor_get(v_toEnvExtension_1716_, 2);
v___x_1719_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1720_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1719_, v_ext_1709_, v_env_1717_, v_asyncMode_1718_);
v_funCC_1748_ = lean_ctor_get(v___x_1720_, 2);
lean_inc(v_funCC_1748_);
v___x_1749_ = l_Lean_NameSet_contains(v_funCC_1748_, v_declName_1710_);
lean_dec(v_funCC_1748_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; 
lean_inc(v_declName_1710_);
v___x_1750_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_1710_, v_a_1711_, v_a_1712_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_dec_ref_known(v___x_1750_, 1);
v___y_1722_ = v_a_1712_;
goto v___jp_1721_;
}
else
{
lean_dec(v___x_1720_);
lean_dec(v_declName_1710_);
lean_dec_ref(v_ext_1709_);
return v___x_1750_;
}
}
else
{
v___y_1722_ = v_a_1712_;
goto v___jp_1721_;
}
v___jp_1721_:
{
lean_object* v_funCC_1723_; lean_object* v___x_1724_; lean_object* v_env_1725_; lean_object* v_nextMacroScope_1726_; lean_object* v_ngen_1727_; lean_object* v_auxDeclNGen_1728_; lean_object* v_traceState_1729_; lean_object* v_messages_1730_; lean_object* v_infoState_1731_; lean_object* v_snapshotTasks_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1746_; 
v_funCC_1723_ = lean_ctor_get(v___x_1720_, 2);
lean_inc(v_funCC_1723_);
lean_dec(v___x_1720_);
v___x_1724_ = lean_st_ref_take(v___y_1722_);
v_env_1725_ = lean_ctor_get(v___x_1724_, 0);
v_nextMacroScope_1726_ = lean_ctor_get(v___x_1724_, 1);
v_ngen_1727_ = lean_ctor_get(v___x_1724_, 2);
v_auxDeclNGen_1728_ = lean_ctor_get(v___x_1724_, 3);
v_traceState_1729_ = lean_ctor_get(v___x_1724_, 4);
v_messages_1730_ = lean_ctor_get(v___x_1724_, 6);
v_infoState_1731_ = lean_ctor_get(v___x_1724_, 7);
v_snapshotTasks_1732_ = lean_ctor_get(v___x_1724_, 8);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1746_ == 0)
{
lean_object* v_unused_1747_; 
v_unused_1747_ = lean_ctor_get(v___x_1724_, 5);
lean_dec(v_unused_1747_);
v___x_1734_ = v___x_1724_;
v_isShared_1735_ = v_isSharedCheck_1746_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_snapshotTasks_1732_);
lean_inc(v_infoState_1731_);
lean_inc(v_messages_1730_);
lean_inc(v_traceState_1729_);
lean_inc(v_auxDeclNGen_1728_);
lean_inc(v_ngen_1727_);
lean_inc(v_nextMacroScope_1726_);
lean_inc(v_env_1725_);
lean_dec(v___x_1724_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1746_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___f_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1736_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_declName_1710_, v_funCC_1723_);
lean_dec(v_declName_1710_);
v___f_1737_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0), 2, 1);
lean_closure_set(v___f_1737_, 0, v___x_1736_);
v___x_1738_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1709_, v_env_1725_, v___f_1737_);
v___x_1739_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 5, v___x_1739_);
lean_ctor_set(v___x_1734_, 0, v___x_1738_);
v___x_1741_ = v___x_1734_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_nextMacroScope_1726_);
lean_ctor_set(v_reuseFailAlloc_1745_, 2, v_ngen_1727_);
lean_ctor_set(v_reuseFailAlloc_1745_, 3, v_auxDeclNGen_1728_);
lean_ctor_set(v_reuseFailAlloc_1745_, 4, v_traceState_1729_);
lean_ctor_set(v_reuseFailAlloc_1745_, 5, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1745_, 6, v_messages_1730_);
lean_ctor_set(v_reuseFailAlloc_1745_, 7, v_infoState_1731_);
lean_ctor_set(v_reuseFailAlloc_1745_, 8, v_snapshotTasks_1732_);
v___x_1741_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1742_ = lean_st_ref_set(v___y_1722_, v___x_1741_);
v___x_1743_ = lean_box(0);
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
return v___x_1744_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object* v_ext_1751_, lean_object* v_declName_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_1751_, v_declName_1752_, v_a_1753_, v_a_1754_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object* v_00_u03b2_1757_, lean_object* v_k_1758_, lean_object* v_t_1759_, lean_object* v_h_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1758_, v_t_1759_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object* v_00_u03b2_1762_, lean_object* v_k_1763_, lean_object* v_t_1764_, lean_object* v_h_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(v_00_u03b2_1762_, v_k_1763_, v_t_1764_, v_h_1765_);
lean_dec(v_k_1763_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object* v_a_1767_, lean_object* v_s_1768_){
_start:
{
lean_object* v_casesTypes_1769_; lean_object* v_extThms_1770_; lean_object* v_funCC_1771_; lean_object* v_inj_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
v_casesTypes_1769_ = lean_ctor_get(v_s_1768_, 0);
v_extThms_1770_ = lean_ctor_get(v_s_1768_, 1);
v_funCC_1771_ = lean_ctor_get(v_s_1768_, 2);
v_inj_1772_ = lean_ctor_get(v_s_1768_, 4);
v_isSharedCheck_1779_ = !lean_is_exclusive(v_s_1768_);
if (v_isSharedCheck_1779_ == 0)
{
lean_object* v_unused_1780_; 
v_unused_1780_ = lean_ctor_get(v_s_1768_, 3);
lean_dec(v_unused_1780_);
v___x_1774_ = v_s_1768_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_inj_1772_);
lean_inc(v_funCC_1771_);
lean_inc(v_extThms_1770_);
lean_inc(v_casesTypes_1769_);
lean_dec(v_s_1768_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 3, v_a_1767_);
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_casesTypes_1769_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_extThms_1770_);
lean_ctor_set(v_reuseFailAlloc_1778_, 2, v_funCC_1771_);
lean_ctor_set(v_reuseFailAlloc_1778_, 3, v_a_1767_);
lean_ctor_set(v_reuseFailAlloc_1778_, 4, v_inj_1772_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
v___x_1782_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
lean_ctor_set(v___x_1782_, 1, v___x_1781_);
lean_ctor_set(v___x_1782_, 2, v___x_1781_);
lean_ctor_set(v___x_1782_, 3, v___x_1781_);
lean_ctor_set(v___x_1782_, 4, v___x_1781_);
lean_ctor_set(v___x_1782_, 5, v___x_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object* v_ext_1783_, lean_object* v_declName_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v___x_1790_; lean_object* v_ext_1791_; lean_object* v_toEnvExtension_1792_; lean_object* v_env_1793_; lean_object* v_asyncMode_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v_ematch_1797_; lean_object* v___x_1798_; 
v___x_1790_ = lean_st_ref_get(v_a_1788_);
v_ext_1791_ = lean_ctor_get(v_ext_1783_, 1);
v_toEnvExtension_1792_ = lean_ctor_get(v_ext_1791_, 0);
v_env_1793_ = lean_ctor_get(v___x_1790_, 0);
lean_inc_ref(v_env_1793_);
lean_dec(v___x_1790_);
v_asyncMode_1794_ = lean_ctor_get(v_toEnvExtension_1792_, 2);
v___x_1795_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1796_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1795_, v_ext_1783_, v_env_1793_, v_asyncMode_1794_);
v_ematch_1797_ = lean_ctor_get(v___x_1796_, 3);
lean_inc_ref(v_ematch_1797_);
lean_dec(v___x_1796_);
v___x_1798_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_ematch_1797_, v_declName_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1843_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1843_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1843_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; lean_object* v_env_1804_; lean_object* v_nextMacroScope_1805_; lean_object* v_ngen_1806_; lean_object* v_auxDeclNGen_1807_; lean_object* v_traceState_1808_; lean_object* v_messages_1809_; lean_object* v_infoState_1810_; lean_object* v_snapshotTasks_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1841_; 
v___x_1803_ = lean_st_ref_take(v_a_1788_);
v_env_1804_ = lean_ctor_get(v___x_1803_, 0);
v_nextMacroScope_1805_ = lean_ctor_get(v___x_1803_, 1);
v_ngen_1806_ = lean_ctor_get(v___x_1803_, 2);
v_auxDeclNGen_1807_ = lean_ctor_get(v___x_1803_, 3);
v_traceState_1808_ = lean_ctor_get(v___x_1803_, 4);
v_messages_1809_ = lean_ctor_get(v___x_1803_, 6);
v_infoState_1810_ = lean_ctor_get(v___x_1803_, 7);
v_snapshotTasks_1811_ = lean_ctor_get(v___x_1803_, 8);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1841_ == 0)
{
lean_object* v_unused_1842_; 
v_unused_1842_ = lean_ctor_get(v___x_1803_, 5);
lean_dec(v_unused_1842_);
v___x_1813_ = v___x_1803_;
v_isShared_1814_ = v_isSharedCheck_1841_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_snapshotTasks_1811_);
lean_inc(v_infoState_1810_);
lean_inc(v_messages_1809_);
lean_inc(v_traceState_1808_);
lean_inc(v_auxDeclNGen_1807_);
lean_inc(v_ngen_1806_);
lean_inc(v_nextMacroScope_1805_);
lean_inc(v_env_1804_);
lean_dec(v___x_1803_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1841_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___f_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___f_1815_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0), 2, 1);
lean_closure_set(v___f_1815_, 0, v_a_1799_);
v___x_1816_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1783_, v_env_1804_, v___f_1815_);
v___x_1817_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 5, v___x_1817_);
lean_ctor_set(v___x_1813_, 0, v___x_1816_);
v___x_1819_ = v___x_1813_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v_nextMacroScope_1805_);
lean_ctor_set(v_reuseFailAlloc_1840_, 2, v_ngen_1806_);
lean_ctor_set(v_reuseFailAlloc_1840_, 3, v_auxDeclNGen_1807_);
lean_ctor_set(v_reuseFailAlloc_1840_, 4, v_traceState_1808_);
lean_ctor_set(v_reuseFailAlloc_1840_, 5, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1840_, 6, v_messages_1809_);
lean_ctor_set(v_reuseFailAlloc_1840_, 7, v_infoState_1810_);
lean_ctor_set(v_reuseFailAlloc_1840_, 8, v_snapshotTasks_1811_);
v___x_1819_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v_mctx_1822_; lean_object* v_zetaDeltaFVarIds_1823_; lean_object* v_postponed_1824_; lean_object* v_diag_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1838_; 
v___x_1820_ = lean_st_ref_set(v_a_1788_, v___x_1819_);
v___x_1821_ = lean_st_ref_take(v_a_1786_);
v_mctx_1822_ = lean_ctor_get(v___x_1821_, 0);
v_zetaDeltaFVarIds_1823_ = lean_ctor_get(v___x_1821_, 2);
v_postponed_1824_ = lean_ctor_get(v___x_1821_, 3);
v_diag_1825_ = lean_ctor_get(v___x_1821_, 4);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1838_ == 0)
{
lean_object* v_unused_1839_; 
v_unused_1839_ = lean_ctor_get(v___x_1821_, 1);
lean_dec(v_unused_1839_);
v___x_1827_ = v___x_1821_;
v_isShared_1828_ = v_isSharedCheck_1838_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_diag_1825_);
lean_inc(v_postponed_1824_);
lean_inc(v_zetaDeltaFVarIds_1823_);
lean_inc(v_mctx_1822_);
lean_dec(v___x_1821_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1838_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1829_; lean_object* v___x_1831_; 
v___x_1829_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 1, v___x_1829_);
v___x_1831_ = v___x_1827_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_mctx_1822_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v___x_1829_);
lean_ctor_set(v_reuseFailAlloc_1837_, 2, v_zetaDeltaFVarIds_1823_);
lean_ctor_set(v_reuseFailAlloc_1837_, 3, v_postponed_1824_);
lean_ctor_set(v_reuseFailAlloc_1837_, 4, v_diag_1825_);
v___x_1831_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1832_ = lean_st_ref_set(v_a_1786_, v___x_1831_);
v___x_1833_ = lean_box(0);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1833_);
v___x_1835_ = v___x_1801_;
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
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec_ref(v_ext_1783_);
v_a_1844_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1798_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1798_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object* v_ext_1852_, lean_object* v_declName_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_1852_, v_declName_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object* v_a_1860_, lean_object* v_s_1861_){
_start:
{
lean_object* v_casesTypes_1862_; lean_object* v_extThms_1863_; lean_object* v_funCC_1864_; lean_object* v_ematch_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
v_casesTypes_1862_ = lean_ctor_get(v_s_1861_, 0);
v_extThms_1863_ = lean_ctor_get(v_s_1861_, 1);
v_funCC_1864_ = lean_ctor_get(v_s_1861_, 2);
v_ematch_1865_ = lean_ctor_get(v_s_1861_, 3);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_s_1861_);
if (v_isSharedCheck_1872_ == 0)
{
lean_object* v_unused_1873_; 
v_unused_1873_ = lean_ctor_get(v_s_1861_, 4);
lean_dec(v_unused_1873_);
v___x_1867_ = v_s_1861_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_ematch_1865_);
lean_inc(v_funCC_1864_);
lean_inc(v_extThms_1863_);
lean_inc(v_casesTypes_1862_);
lean_dec(v_s_1861_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 4, v_a_1860_);
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_casesTypes_1862_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v_extThms_1863_);
lean_ctor_set(v_reuseFailAlloc_1871_, 2, v_funCC_1864_);
lean_ctor_set(v_reuseFailAlloc_1871_, 3, v_ematch_1865_);
lean_ctor_set(v_reuseFailAlloc_1871_, 4, v_a_1860_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object* v_ext_1874_, lean_object* v_declName_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_){
_start:
{
lean_object* v___x_1881_; lean_object* v_ext_1882_; lean_object* v_toEnvExtension_1883_; lean_object* v_env_1884_; lean_object* v_asyncMode_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v_inj_1888_; lean_object* v___x_1889_; 
v___x_1881_ = lean_st_ref_get(v_a_1879_);
v_ext_1882_ = lean_ctor_get(v_ext_1874_, 1);
v_toEnvExtension_1883_ = lean_ctor_get(v_ext_1882_, 0);
v_env_1884_ = lean_ctor_get(v___x_1881_, 0);
lean_inc_ref(v_env_1884_);
lean_dec(v___x_1881_);
v_asyncMode_1885_ = lean_ctor_get(v_toEnvExtension_1883_, 2);
v___x_1886_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1887_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1886_, v_ext_1874_, v_env_1884_, v_asyncMode_1885_);
v_inj_1888_ = lean_ctor_get(v___x_1887_, 4);
lean_inc_ref(v_inj_1888_);
lean_dec(v___x_1887_);
v___x_1889_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_inj_1888_, v_declName_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1934_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1892_ = v___x_1889_;
v_isShared_1893_ = v_isSharedCheck_1934_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1889_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1934_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; lean_object* v_env_1895_; lean_object* v_nextMacroScope_1896_; lean_object* v_ngen_1897_; lean_object* v_auxDeclNGen_1898_; lean_object* v_traceState_1899_; lean_object* v_messages_1900_; lean_object* v_infoState_1901_; lean_object* v_snapshotTasks_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1932_; 
v___x_1894_ = lean_st_ref_take(v_a_1879_);
v_env_1895_ = lean_ctor_get(v___x_1894_, 0);
v_nextMacroScope_1896_ = lean_ctor_get(v___x_1894_, 1);
v_ngen_1897_ = lean_ctor_get(v___x_1894_, 2);
v_auxDeclNGen_1898_ = lean_ctor_get(v___x_1894_, 3);
v_traceState_1899_ = lean_ctor_get(v___x_1894_, 4);
v_messages_1900_ = lean_ctor_get(v___x_1894_, 6);
v_infoState_1901_ = lean_ctor_get(v___x_1894_, 7);
v_snapshotTasks_1902_ = lean_ctor_get(v___x_1894_, 8);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; 
v_unused_1933_ = lean_ctor_get(v___x_1894_, 5);
lean_dec(v_unused_1933_);
v___x_1904_ = v___x_1894_;
v_isShared_1905_ = v_isSharedCheck_1932_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_snapshotTasks_1902_);
lean_inc(v_infoState_1901_);
lean_inc(v_messages_1900_);
lean_inc(v_traceState_1899_);
lean_inc(v_auxDeclNGen_1898_);
lean_inc(v_ngen_1897_);
lean_inc(v_nextMacroScope_1896_);
lean_inc(v_env_1895_);
lean_dec(v___x_1894_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1932_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___f_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___f_1906_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0), 2, 1);
lean_closure_set(v___f_1906_, 0, v_a_1890_);
v___x_1907_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1874_, v_env_1895_, v___f_1906_);
v___x_1908_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 5, v___x_1908_);
lean_ctor_set(v___x_1904_, 0, v___x_1907_);
v___x_1910_ = v___x_1904_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1907_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_nextMacroScope_1896_);
lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_ngen_1897_);
lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_auxDeclNGen_1898_);
lean_ctor_set(v_reuseFailAlloc_1931_, 4, v_traceState_1899_);
lean_ctor_set(v_reuseFailAlloc_1931_, 5, v___x_1908_);
lean_ctor_set(v_reuseFailAlloc_1931_, 6, v_messages_1900_);
lean_ctor_set(v_reuseFailAlloc_1931_, 7, v_infoState_1901_);
lean_ctor_set(v_reuseFailAlloc_1931_, 8, v_snapshotTasks_1902_);
v___x_1910_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v_mctx_1913_; lean_object* v_zetaDeltaFVarIds_1914_; lean_object* v_postponed_1915_; lean_object* v_diag_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1929_; 
v___x_1911_ = lean_st_ref_set(v_a_1879_, v___x_1910_);
v___x_1912_ = lean_st_ref_take(v_a_1877_);
v_mctx_1913_ = lean_ctor_get(v___x_1912_, 0);
v_zetaDeltaFVarIds_1914_ = lean_ctor_get(v___x_1912_, 2);
v_postponed_1915_ = lean_ctor_get(v___x_1912_, 3);
v_diag_1916_ = lean_ctor_get(v___x_1912_, 4);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1929_ == 0)
{
lean_object* v_unused_1930_; 
v_unused_1930_ = lean_ctor_get(v___x_1912_, 1);
lean_dec(v_unused_1930_);
v___x_1918_ = v___x_1912_;
v_isShared_1919_ = v_isSharedCheck_1929_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_diag_1916_);
lean_inc(v_postponed_1915_);
lean_inc(v_zetaDeltaFVarIds_1914_);
lean_inc(v_mctx_1913_);
lean_dec(v___x_1912_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1929_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; lean_object* v___x_1922_; 
v___x_1920_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 1, v___x_1920_);
v___x_1922_ = v___x_1918_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_mctx_1913_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_1928_, 2, v_zetaDeltaFVarIds_1914_);
lean_ctor_set(v_reuseFailAlloc_1928_, 3, v_postponed_1915_);
lean_ctor_set(v_reuseFailAlloc_1928_, 4, v_diag_1916_);
v___x_1922_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1923_ = lean_st_ref_set(v_a_1877_, v___x_1922_);
v___x_1924_ = lean_box(0);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v___x_1924_);
v___x_1926_ = v___x_1892_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
lean_dec_ref(v_ext_1874_);
v_a_1935_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1889_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1889_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object* v_ext_1943_, lean_object* v_declName_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_1943_, v_declName_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
lean_dec(v_a_1948_);
lean_dec_ref(v_a_1947_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
return v_res_1950_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1951_, lean_object* v_i_1952_, lean_object* v_k_1953_){
_start:
{
lean_object* v___x_1954_; uint8_t v___x_1955_; 
v___x_1954_ = lean_array_get_size(v_keys_1951_);
v___x_1955_ = lean_nat_dec_lt(v_i_1952_, v___x_1954_);
if (v___x_1955_ == 0)
{
lean_dec(v_i_1952_);
return v___x_1955_;
}
else
{
lean_object* v_k_x27_1956_; uint8_t v___x_1957_; 
v_k_x27_1956_ = lean_array_fget_borrowed(v_keys_1951_, v_i_1952_);
v___x_1957_ = lean_name_eq(v_k_1953_, v_k_x27_1956_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = lean_unsigned_to_nat(1u);
v___x_1959_ = lean_nat_add(v_i_1952_, v___x_1958_);
lean_dec(v_i_1952_);
v_i_1952_ = v___x_1959_;
goto _start;
}
else
{
lean_dec(v_i_1952_);
return v___x_1957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1961_, lean_object* v_i_1962_, lean_object* v_k_1963_){
_start:
{
uint8_t v_res_1964_; lean_object* v_r_1965_; 
v_res_1964_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_1961_, v_i_1962_, v_k_1963_);
lean_dec(v_k_1963_);
lean_dec_ref(v_keys_1961_);
v_r_1965_ = lean_box(v_res_1964_);
return v_r_1965_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object* v_x_1966_, size_t v_x_1967_, lean_object* v_x_1968_){
_start:
{
if (lean_obj_tag(v_x_1966_) == 0)
{
lean_object* v_es_1969_; lean_object* v___x_1970_; size_t v___x_1971_; size_t v___x_1972_; lean_object* v_j_1973_; lean_object* v___x_1974_; 
v_es_1969_ = lean_ctor_get(v_x_1966_, 0);
v___x_1970_ = lean_box(2);
v___x_1971_ = ((size_t)31ULL);
v___x_1972_ = lean_usize_land(v_x_1967_, v___x_1971_);
v_j_1973_ = lean_usize_to_nat(v___x_1972_);
v___x_1974_ = lean_array_get_borrowed(v___x_1970_, v_es_1969_, v_j_1973_);
lean_dec(v_j_1973_);
switch(lean_obj_tag(v___x_1974_))
{
case 0:
{
lean_object* v_key_1975_; uint8_t v___x_1976_; 
v_key_1975_ = lean_ctor_get(v___x_1974_, 0);
v___x_1976_ = lean_name_eq(v_x_1968_, v_key_1975_);
return v___x_1976_;
}
case 1:
{
lean_object* v_node_1977_; size_t v___x_1978_; size_t v___x_1979_; 
v_node_1977_ = lean_ctor_get(v___x_1974_, 0);
v___x_1978_ = ((size_t)5ULL);
v___x_1979_ = lean_usize_shift_right(v_x_1967_, v___x_1978_);
v_x_1966_ = v_node_1977_;
v_x_1967_ = v___x_1979_;
goto _start;
}
default: 
{
uint8_t v___x_1981_; 
v___x_1981_ = 0;
return v___x_1981_;
}
}
}
else
{
lean_object* v_ks_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; 
v_ks_1982_ = lean_ctor_get(v_x_1966_, 0);
v___x_1983_ = lean_unsigned_to_nat(0u);
v___x_1984_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_ks_1982_, v___x_1983_, v_x_1968_);
return v___x_1984_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_1985_, lean_object* v_x_1986_, lean_object* v_x_1987_){
_start:
{
size_t v_x_327__boxed_1988_; uint8_t v_res_1989_; lean_object* v_r_1990_; 
v_x_327__boxed_1988_ = lean_unbox_usize(v_x_1986_);
lean_dec(v_x_1986_);
v_res_1989_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_1985_, v_x_327__boxed_1988_, v_x_1987_);
lean_dec(v_x_1987_);
lean_dec_ref(v_x_1985_);
v_r_1990_ = lean_box(v_res_1989_);
return v_r_1990_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1991_; uint64_t v___x_1992_; 
v___x_1991_ = lean_unsigned_to_nat(1723u);
v___x_1992_ = lean_uint64_of_nat(v___x_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object* v_x_1993_, lean_object* v_x_1994_){
_start:
{
uint64_t v___y_1996_; 
if (lean_obj_tag(v_x_1994_) == 0)
{
uint64_t v___x_1999_; 
v___x_1999_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_1996_ = v___x_1999_;
goto v___jp_1995_;
}
else
{
uint64_t v_hash_2000_; 
v_hash_2000_ = lean_ctor_get_uint64(v_x_1994_, sizeof(void*)*2);
v___y_1996_ = v_hash_2000_;
goto v___jp_1995_;
}
v___jp_1995_:
{
size_t v___x_1997_; uint8_t v___x_1998_; 
v___x_1997_ = lean_uint64_to_usize(v___y_1996_);
v___x_1998_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_1993_, v___x_1997_, v_x_1994_);
return v___x_1998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object* v_x_2001_, lean_object* v_x_2002_){
_start:
{
uint8_t v_res_2003_; lean_object* v_r_2004_; 
v_res_2003_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_2001_, v_x_2002_);
lean_dec(v_x_2002_);
lean_dec_ref(v_x_2001_);
v_r_2004_ = lean_box(v_res_2003_);
return v_r_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object* v_ext_2005_, lean_object* v_declName_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v___x_2009_; lean_object* v_ext_2010_; lean_object* v_toEnvExtension_2011_; lean_object* v_env_2012_; lean_object* v_asyncMode_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v_extThms_2016_; uint8_t v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2009_ = lean_st_ref_get(v_a_2007_);
v_ext_2010_ = lean_ctor_get(v_ext_2005_, 1);
v_toEnvExtension_2011_ = lean_ctor_get(v_ext_2010_, 0);
v_env_2012_ = lean_ctor_get(v___x_2009_, 0);
lean_inc_ref(v_env_2012_);
lean_dec(v___x_2009_);
v_asyncMode_2013_ = lean_ctor_get(v_toEnvExtension_2011_, 2);
v___x_2014_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2015_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2014_, v_ext_2005_, v_env_2012_, v_asyncMode_2013_);
v_extThms_2016_ = lean_ctor_get(v___x_2015_, 1);
lean_inc_ref(v_extThms_2016_);
lean_dec(v___x_2015_);
v___x_2017_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_extThms_2016_, v_declName_2006_);
lean_dec_ref(v_extThms_2016_);
v___x_2018_ = lean_box(v___x_2017_);
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object* v_ext_2020_, lean_object* v_declName_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2020_, v_declName_2021_, v_a_2022_);
lean_dec(v_a_2022_);
lean_dec(v_declName_2021_);
lean_dec_ref(v_ext_2020_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object* v_ext_2025_, lean_object* v_declName_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2025_, v_declName_2026_, v_a_2028_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object* v_ext_2031_, lean_object* v_declName_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(v_ext_2031_, v_declName_2032_, v_a_2033_, v_a_2034_);
lean_dec(v_a_2034_);
lean_dec_ref(v_a_2033_);
lean_dec(v_declName_2032_);
lean_dec_ref(v_ext_2031_);
return v_res_2036_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object* v_00_u03b2_2037_, lean_object* v_x_2038_, lean_object* v_x_2039_){
_start:
{
uint8_t v___x_2040_; 
v___x_2040_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_2038_, v_x_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object* v_00_u03b2_2041_, lean_object* v_x_2042_, lean_object* v_x_2043_){
_start:
{
uint8_t v_res_2044_; lean_object* v_r_2045_; 
v_res_2044_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(v_00_u03b2_2041_, v_x_2042_, v_x_2043_);
lean_dec(v_x_2043_);
lean_dec_ref(v_x_2042_);
v_r_2045_ = lean_box(v_res_2044_);
return v_r_2045_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_2046_, lean_object* v_x_2047_, size_t v_x_2048_, lean_object* v_x_2049_){
_start:
{
uint8_t v___x_2050_; 
v___x_2050_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2047_, v_x_2048_, v_x_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2051_, lean_object* v_x_2052_, lean_object* v_x_2053_, lean_object* v_x_2054_){
_start:
{
size_t v_x_418__boxed_2055_; uint8_t v_res_2056_; lean_object* v_r_2057_; 
v_x_418__boxed_2055_ = lean_unbox_usize(v_x_2053_);
lean_dec(v_x_2053_);
v_res_2056_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(v_00_u03b2_2051_, v_x_2052_, v_x_418__boxed_2055_, v_x_2054_);
lean_dec(v_x_2054_);
lean_dec_ref(v_x_2052_);
v_r_2057_ = lean_box(v_res_2056_);
return v_r_2057_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2058_, lean_object* v_keys_2059_, lean_object* v_vals_2060_, lean_object* v_heq_2061_, lean_object* v_i_2062_, lean_object* v_k_2063_){
_start:
{
uint8_t v___x_2064_; 
v___x_2064_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_2059_, v_i_2062_, v_k_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2065_, lean_object* v_keys_2066_, lean_object* v_vals_2067_, lean_object* v_heq_2068_, lean_object* v_i_2069_, lean_object* v_k_2070_){
_start:
{
uint8_t v_res_2071_; lean_object* v_r_2072_; 
v_res_2071_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(v_00_u03b2_2065_, v_keys_2066_, v_vals_2067_, v_heq_2068_, v_i_2069_, v_k_2070_);
lean_dec(v_k_2070_);
lean_dec_ref(v_vals_2067_);
lean_dec_ref(v_keys_2066_);
v_r_2072_ = lean_box(v_res_2071_);
return v_r_2072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object* v_ext_2073_, lean_object* v_declName_2074_, lean_object* v_a_2075_){
_start:
{
lean_object* v___x_2077_; lean_object* v_ext_2078_; lean_object* v_toEnvExtension_2079_; lean_object* v_env_2080_; lean_object* v_asyncMode_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v_inj_2084_; lean_object* v___x_2085_; uint8_t v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2077_ = lean_st_ref_get(v_a_2075_);
v_ext_2078_ = lean_ctor_get(v_ext_2073_, 1);
v_toEnvExtension_2079_ = lean_ctor_get(v_ext_2078_, 0);
v_env_2080_ = lean_ctor_get(v___x_2077_, 0);
lean_inc_ref(v_env_2080_);
lean_dec(v___x_2077_);
v_asyncMode_2081_ = lean_ctor_get(v_toEnvExtension_2079_, 2);
v___x_2082_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2083_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2082_, v_ext_2073_, v_env_2080_, v_asyncMode_2081_);
v_inj_2084_ = lean_ctor_get(v___x_2083_, 4);
lean_inc_ref(v_inj_2084_);
lean_dec(v___x_2083_);
v___x_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2085_, 0, v_declName_2074_);
v___x_2086_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_inj_2084_, v___x_2085_);
lean_dec_ref_known(v___x_2085_, 1);
lean_dec_ref(v_inj_2084_);
v___x_2087_ = lean_box(v___x_2086_);
v___x_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object* v_ext_2089_, lean_object* v_declName_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2089_, v_declName_2090_, v_a_2091_);
lean_dec(v_a_2091_);
lean_dec_ref(v_ext_2089_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object* v_ext_2094_, lean_object* v_declName_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2094_, v_declName_2095_, v_a_2097_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object* v_ext_2100_, lean_object* v_declName_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(v_ext_2100_, v_declName_2101_, v_a_2102_, v_a_2103_);
lean_dec(v_a_2103_);
lean_dec_ref(v_a_2102_);
lean_dec_ref(v_ext_2100_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object* v_ext_2106_, lean_object* v_declName_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v___x_2110_; lean_object* v_ext_2111_; lean_object* v_toEnvExtension_2112_; lean_object* v_env_2113_; lean_object* v_asyncMode_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v_funCC_2117_; uint8_t v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2110_ = lean_st_ref_get(v_a_2108_);
v_ext_2111_ = lean_ctor_get(v_ext_2106_, 1);
v_toEnvExtension_2112_ = lean_ctor_get(v_ext_2111_, 0);
v_env_2113_ = lean_ctor_get(v___x_2110_, 0);
lean_inc_ref(v_env_2113_);
lean_dec(v___x_2110_);
v_asyncMode_2114_ = lean_ctor_get(v_toEnvExtension_2112_, 2);
v___x_2115_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2116_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2115_, v_ext_2106_, v_env_2113_, v_asyncMode_2114_);
v_funCC_2117_ = lean_ctor_get(v___x_2116_, 2);
lean_inc(v_funCC_2117_);
lean_dec(v___x_2116_);
v___x_2118_ = l_Lean_NameSet_contains(v_funCC_2117_, v_declName_2107_);
lean_dec(v_funCC_2117_);
v___x_2119_ = lean_box(v___x_2118_);
v___x_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object* v_ext_2121_, lean_object* v_declName_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2121_, v_declName_2122_, v_a_2123_);
lean_dec(v_a_2123_);
lean_dec(v_declName_2122_);
lean_dec_ref(v_ext_2121_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object* v_ext_2126_, lean_object* v_declName_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2126_, v_declName_2127_, v_a_2129_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object* v_ext_2132_, lean_object* v_declName_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(v_ext_2132_, v_declName_2133_, v_a_2134_, v_a_2135_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
lean_dec(v_declName_2133_);
lean_dec_ref(v_ext_2132_);
return v_res_2137_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7));
v___x_2162_ = l_Lean_mkAtom(v___x_2161_);
return v___x_2162_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2163_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9);
v___x_2164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2165_ = lean_array_push(v___x_2164_, v___x_2163_);
return v___x_2165_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14));
v___x_2175_ = l_Lean_mkAtom(v___x_2174_);
return v___x_2175_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15);
v___x_2177_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2178_ = lean_array_push(v___x_2177_, v___x_2176_);
return v___x_2178_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17(void){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2179_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16);
v___x_2180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13));
v___x_2181_ = lean_box(2);
v___x_2182_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
lean_ctor_set(v___x_2182_, 1, v___x_2180_);
lean_ctor_set(v___x_2182_, 2, v___x_2179_);
return v___x_2182_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2183_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17);
v___x_2184_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10);
v___x_2185_ = lean_array_push(v___x_2184_, v___x_2183_);
return v___x_2185_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2186_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18);
v___x_2187_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8));
v___x_2188_ = lean_box(2);
v___x_2189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
lean_ctor_set(v___x_2189_, 1, v___x_2187_);
lean_ctor_set(v___x_2189_, 2, v___x_2186_);
return v___x_2189_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19);
v___x_2191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2192_ = lean_array_push(v___x_2191_, v___x_2190_);
return v___x_2192_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2193_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20);
v___x_2194_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6));
v___x_2195_ = lean_box(2);
v___x_2196_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
lean_ctor_set(v___x_2196_, 1, v___x_2194_);
lean_ctor_set(v___x_2196_, 2, v___x_2193_);
return v___x_2196_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21);
v___x_2198_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2199_ = lean_array_push(v___x_2198_, v___x_2197_);
return v___x_2199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2200_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22);
v___x_2201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4));
v___x_2202_ = lean_box(2);
v___x_2203_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
lean_ctor_set(v___x_2203_, 1, v___x_2201_);
lean_ctor_set(v___x_2203_, 2, v___x_2200_);
return v___x_2203_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2204_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23);
v___x_2205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2206_ = lean_array_push(v___x_2205_, v___x_2204_);
return v___x_2206_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2207_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24);
v___x_2208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1));
v___x_2209_ = lean_box(2);
v___x_2210_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
lean_ctor_set(v___x_2210_, 1, v___x_2208_);
lean_ctor_set(v___x_2210_, 2, v___x_2207_);
return v___x_2210_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1(void){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object* v_declName_2212_, lean_object* v_ext_2213_, lean_object* v_____r_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
uint8_t v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = 0;
lean_inc(v_declName_2212_);
v___x_2221_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_2212_, v___x_2220_, v___y_2217_, v___y_2218_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; uint8_t v___x_2223_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref_known(v___x_2221_, 1);
v___x_2223_ = lean_unbox(v_a_2222_);
lean_dec(v_a_2222_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2224_; lean_object* v_a_2225_; uint8_t v___x_2226_; 
v___x_2224_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2213_, v_declName_2212_, v___y_2218_);
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref(v___x_2224_);
v___x_2226_ = lean_unbox(v_a_2225_);
lean_dec(v_a_2225_);
if (v___x_2226_ == 0)
{
lean_object* v___x_2227_; lean_object* v_a_2228_; uint8_t v___x_2229_; 
lean_inc(v_declName_2212_);
v___x_2227_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2213_, v_declName_2212_, v___y_2218_);
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
lean_dec_ref(v___x_2227_);
v___x_2229_ = lean_unbox(v_a_2228_);
lean_dec(v_a_2228_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; lean_object* v_a_2231_; uint8_t v___x_2232_; 
v___x_2230_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2213_, v_declName_2212_, v___y_2218_);
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
lean_dec_ref(v___x_2230_);
v___x_2232_ = lean_unbox(v_a_2231_);
lean_dec(v_a_2231_);
if (v___x_2232_ == 0)
{
lean_object* v___x_2233_; 
v___x_2233_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_2213_, v_declName_2212_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
return v___x_2233_;
}
else
{
lean_object* v___x_2234_; 
v___x_2234_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_2213_, v_declName_2212_, v___y_2217_, v___y_2218_);
return v___x_2234_;
}
}
else
{
lean_object* v___x_2235_; 
v___x_2235_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_2213_, v_declName_2212_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
return v___x_2235_;
}
}
else
{
lean_object* v___x_2236_; 
v___x_2236_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_2213_, v_declName_2212_, v___y_2217_, v___y_2218_);
return v___x_2236_;
}
}
else
{
lean_object* v___x_2237_; 
v___x_2237_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_2213_, v_declName_2212_, v___y_2217_, v___y_2218_);
return v___x_2237_;
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec_ref(v_ext_2213_);
lean_dec(v_declName_2212_);
v_a_2238_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2221_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2221_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object* v_declName_2246_, lean_object* v_ext_2247_, lean_object* v_____r_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2246_, v_ext_2247_, v_____r_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(lean_object* v_msgData_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v___x_2261_; lean_object* v_env_2262_; lean_object* v___x_2263_; lean_object* v_mctx_2264_; lean_object* v_lctx_2265_; lean_object* v_options_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2261_ = lean_st_ref_get(v___y_2259_);
v_env_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc_ref(v_env_2262_);
lean_dec(v___x_2261_);
v___x_2263_ = lean_st_ref_get(v___y_2257_);
v_mctx_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc_ref(v_mctx_2264_);
lean_dec(v___x_2263_);
v_lctx_2265_ = lean_ctor_get(v___y_2256_, 2);
v_options_2266_ = lean_ctor_get(v___y_2258_, 2);
lean_inc_ref(v_options_2266_);
lean_inc_ref(v_lctx_2265_);
v___x_2267_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2267_, 0, v_env_2262_);
lean_ctor_set(v___x_2267_, 1, v_mctx_2264_);
lean_ctor_set(v___x_2267_, 2, v_lctx_2265_);
lean_ctor_set(v___x_2267_, 3, v_options_2266_);
v___x_2268_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
lean_ctor_set(v___x_2268_, 1, v_msgData_2255_);
v___x_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0___boxed(lean_object* v_msgData_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msgData_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object* v_msg_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_ref_2283_; lean_object* v___x_2284_; lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2293_; 
v_ref_2283_ = lean_ctor_get(v___y_2280_, 5);
v___x_2284_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2287_ = v___x_2284_;
v_isShared_2288_ = v_isSharedCheck_2293_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2284_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2293_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2289_; lean_object* v___x_2291_; 
lean_inc(v_ref_2283_);
v___x_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2289_, 0, v_ref_2283_);
lean_ctor_set(v___x_2289_, 1, v_a_2285_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set_tag(v___x_2287_, 1);
lean_ctor_set(v___x_2287_, 0, v___x_2289_);
v___x_2291_ = v___x_2287_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2289_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object* v_msg_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
return v_res_2300_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2307_; uint64_t v___x_2308_; 
v___x_2307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2308_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2307_);
return v___x_2308_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2309_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1);
v___x_2310_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2311_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
lean_ctor_set_uint64(v___x_2311_, sizeof(void*)*1, v___x_2309_);
return v___x_2311_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2312_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
return v___x_2314_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2315_ = lean_box(1);
v___x_2316_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2317_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2318_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
lean_ctor_set(v___x_2318_, 1, v___x_2316_);
lean_ctor_set(v___x_2318_, 2, v___x_2315_);
return v___x_2318_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2321_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2322_ = lean_unsigned_to_nat(0u);
v___x_2323_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
lean_ctor_set(v___x_2323_, 2, v___x_2322_);
lean_ctor_set(v___x_2323_, 3, v___x_2322_);
lean_ctor_set(v___x_2323_, 4, v___x_2321_);
lean_ctor_set(v___x_2323_, 5, v___x_2321_);
lean_ctor_set(v___x_2323_, 6, v___x_2321_);
lean_ctor_set(v___x_2323_, 7, v___x_2321_);
lean_ctor_set(v___x_2323_, 8, v___x_2321_);
lean_ctor_set(v___x_2323_, 9, v___x_2321_);
return v___x_2323_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2325_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
lean_ctor_set(v___x_2325_, 2, v___x_2324_);
lean_ctor_set(v___x_2325_, 3, v___x_2324_);
lean_ctor_set(v___x_2325_, 4, v___x_2324_);
lean_ctor_set(v___x_2325_, 5, v___x_2324_);
return v___x_2325_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9(void){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
lean_ctor_set(v___x_2327_, 2, v___x_2326_);
lean_ctor_set(v___x_2327_, 3, v___x_2326_);
lean_ctor_set(v___x_2327_, 4, v___x_2326_);
return v___x_2327_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10));
v___x_2330_ = l_Lean_stringToMessageData(v___x_2329_);
return v___x_2330_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13(void){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12));
v___x_2333_ = l_Lean_stringToMessageData(v___x_2332_);
return v___x_2333_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15(void){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14));
v___x_2336_ = l_Lean_stringToMessageData(v___x_2335_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object* v___x_2337_, lean_object* v_ext_2338_, uint8_t v_showInfo_2339_, lean_object* v_attrName_2340_, lean_object* v_declName_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
uint8_t v___x_2345_; uint8_t v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___y_2360_; 
v___x_2345_ = 1;
v___x_2346_ = 0;
v___x_2347_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_2348_ = lean_unsigned_to_nat(0u);
v___x_2349_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2350_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5);
v___x_2351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6));
v___x_2352_ = lean_box(0);
lean_inc(v___x_2337_);
v___x_2353_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2353_, 0, v___x_2347_);
lean_ctor_set(v___x_2353_, 1, v___x_2337_);
lean_ctor_set(v___x_2353_, 2, v___x_2350_);
lean_ctor_set(v___x_2353_, 3, v___x_2351_);
lean_ctor_set(v___x_2353_, 4, v___x_2352_);
lean_ctor_set(v___x_2353_, 5, v___x_2348_);
lean_ctor_set(v___x_2353_, 6, v___x_2352_);
lean_ctor_set_uint8(v___x_2353_, sizeof(void*)*7, v___x_2346_);
lean_ctor_set_uint8(v___x_2353_, sizeof(void*)*7 + 1, v___x_2346_);
lean_ctor_set_uint8(v___x_2353_, sizeof(void*)*7 + 2, v___x_2346_);
lean_ctor_set_uint8(v___x_2353_, sizeof(void*)*7 + 3, v___x_2345_);
v___x_2354_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_2355_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_2356_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9);
v___x_2357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2354_);
lean_ctor_set(v___x_2357_, 1, v___x_2355_);
lean_ctor_set(v___x_2357_, 2, v___x_2337_);
lean_ctor_set(v___x_2357_, 3, v___x_2349_);
lean_ctor_set(v___x_2357_, 4, v___x_2356_);
v___x_2358_ = lean_st_mk_ref(v___x_2357_);
if (v_showInfo_2339_ == 0)
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
lean_dec(v_attrName_2340_);
v___x_2370_ = lean_box(0);
v___x_2371_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2341_, v_ext_2338_, v___x_2370_, v___x_2353_, v___x_2358_, v___y_2342_, v___y_2343_);
lean_dec_ref_known(v___x_2353_, 7);
v___y_2360_ = v___x_2371_;
goto v___jp_2359_;
}
else
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
lean_dec(v_declName_2341_);
lean_dec_ref(v_ext_2338_);
v___x_2372_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11);
v___x_2373_ = l_Lean_MessageData_ofName(v_attrName_2340_);
lean_inc_ref(v___x_2373_);
v___x_2374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2372_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13);
v___x_2376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2374_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
v___x_2377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
lean_ctor_set(v___x_2377_, 1, v___x_2373_);
v___x_2378_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15);
v___x_2379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2377_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
v___x_2380_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2379_, v___x_2353_, v___x_2358_, v___y_2342_, v___y_2343_);
lean_dec_ref_known(v___x_2353_, 7);
v___y_2360_ = v___x_2380_;
goto v___jp_2359_;
}
v___jp_2359_:
{
if (lean_obj_tag(v___y_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2369_; 
v_a_2361_ = lean_ctor_get(v___y_2360_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___y_2360_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2363_ = v___y_2360_;
v_isShared_2364_ = v_isSharedCheck_2369_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___y_2360_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2369_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2365_; lean_object* v___x_2367_; 
v___x_2365_ = lean_st_ref_get(v___x_2358_);
lean_dec(v___x_2358_);
lean_dec(v___x_2365_);
if (v_isShared_2364_ == 0)
{
v___x_2367_ = v___x_2363_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2361_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
else
{
lean_dec(v___x_2358_);
return v___y_2360_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object* v___x_2381_, lean_object* v_ext_2382_, lean_object* v_showInfo_2383_, lean_object* v_attrName_2384_, lean_object* v_declName_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
uint8_t v_showInfo_boxed_2389_; lean_object* v_res_2390_; 
v_showInfo_boxed_2389_ = lean_unbox(v_showInfo_2383_);
v_res_2390_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(v___x_2381_, v_ext_2382_, v_showInfo_boxed_2389_, v_attrName_2384_, v_declName_2385_, v___y_2386_, v___y_2387_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object* v_ext_2393_, uint8_t v_attrKind_2394_, uint8_t v_showInfo_2395_, uint8_t v_minIndexable_2396_, lean_object* v_as_x27_2397_, lean_object* v_b_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
if (lean_obj_tag(v_as_x27_2397_) == 0)
{
lean_object* v___x_2404_; 
lean_dec_ref(v_ext_2393_);
v___x_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2404_, 0, v_b_2398_);
return v___x_2404_;
}
else
{
lean_object* v_head_2405_; lean_object* v_tail_2406_; lean_object* v___x_2407_; 
v_head_2405_ = lean_ctor_get(v_as_x27_2397_, 0);
v_tail_2406_ = lean_ctor_get(v_as_x27_2397_, 1);
v___x_2407_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2402_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2407_, 1);
v___x_2409_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0));
lean_inc(v_head_2405_);
lean_inc_ref(v_ext_2393_);
v___x_2410_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2393_, v_head_2405_, v_attrKind_2394_, v___x_2409_, v_a_2408_, v_showInfo_2395_, v_minIndexable_2396_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v___x_2411_; 
lean_dec_ref_known(v___x_2410_, 1);
v___x_2411_ = lean_box(0);
v_as_x27_2397_ = v_tail_2406_;
v_b_2398_ = v___x_2411_;
goto _start;
}
else
{
lean_dec_ref(v_ext_2393_);
return v___x_2410_;
}
}
else
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
lean_dec_ref(v_ext_2393_);
v_a_2413_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2407_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2407_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object* v_ext_2421_, lean_object* v_attrKind_2422_, lean_object* v_showInfo_2423_, lean_object* v_minIndexable_2424_, lean_object* v_as_x27_2425_, lean_object* v_b_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
uint8_t v_attrKind_boxed_2432_; uint8_t v_showInfo_boxed_2433_; uint8_t v_minIndexable_boxed_2434_; lean_object* v_res_2435_; 
v_attrKind_boxed_2432_ = lean_unbox(v_attrKind_2422_);
v_showInfo_boxed_2433_ = lean_unbox(v_showInfo_2423_);
v_minIndexable_boxed_2434_ = lean_unbox(v_minIndexable_2424_);
v_res_2435_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2421_, v_attrKind_boxed_2432_, v_showInfo_boxed_2433_, v_minIndexable_boxed_2434_, v_as_x27_2425_, v_b_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v_as_x27_2425_);
return v_res_2435_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0));
v___x_2438_ = l_Lean_stringToMessageData(v___x_2437_);
return v___x_2438_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4(void){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3));
v___x_2442_ = l_Lean_stringToMessageData(v___x_2441_);
return v___x_2442_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5));
v___x_2445_ = l_Lean_stringToMessageData(v___x_2444_);
return v___x_2445_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8(void){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7));
v___x_2448_ = l_Lean_stringToMessageData(v___x_2447_);
return v___x_2448_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12(void){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11));
v___x_2454_ = l_Lean_stringToMessageData(v___x_2453_);
return v___x_2454_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13));
v___x_2457_ = l_Lean_stringToMessageData(v___x_2456_);
return v___x_2457_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16(void){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15));
v___x_2460_ = l_Lean_stringToMessageData(v___x_2459_);
return v___x_2460_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18(void){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2462_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17));
v___x_2463_ = l_Lean_stringToMessageData(v___x_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object* v_stx_2464_, lean_object* v_ext_2465_, lean_object* v_declName_2466_, uint8_t v_attrKind_2467_, uint8_t v_showInfo_2468_, uint8_t v_minIndexable_2469_, uint8_t v___x_2470_, lean_object* v_attrName_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2481_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___x_2513_; 
v___x_2513_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_2464_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_a_2514_);
lean_dec_ref_known(v___x_2513_, 1);
switch(lean_obj_tag(v_a_2514_))
{
case 0:
{
lean_object* v_k_2515_; 
lean_dec(v_attrName_2471_);
lean_dec(v_stx_2464_);
v_k_2515_ = lean_ctor_get(v_a_2514_, 0);
lean_inc(v_k_2515_);
lean_dec_ref_known(v_a_2514_, 1);
if (lean_obj_tag(v_k_2515_) == 9)
{
lean_object* v___x_2516_; 
lean_dec(v_declName_2466_);
lean_dec_ref(v_ext_2465_);
v___x_2516_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___y_2474_, v___y_2475_);
return v___x_2516_;
}
else
{
lean_object* v___x_2517_; 
v___x_2517_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2475_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2519_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2518_);
lean_dec_ref_known(v___x_2517_, 1);
v___x_2519_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2465_, v_declName_2466_, v_attrKind_2467_, v_k_2515_, v_a_2518_, v_showInfo_2468_, v_minIndexable_2469_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2519_;
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_dec(v_k_2515_);
lean_dec(v_declName_2466_);
lean_dec_ref(v_ext_2465_);
v_a_2520_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2517_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2517_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
}
case 1:
{
uint8_t v_eager_2528_; lean_object* v___x_2529_; 
lean_dec(v_attrName_2471_);
lean_dec(v_stx_2464_);
v_eager_2528_ = lean_ctor_get_uint8(v_a_2514_, 0);
lean_dec_ref_known(v_a_2514_, 0);
v___x_2529_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2465_, v_declName_2466_, v_eager_2528_, v_attrKind_2467_, v___y_2474_, v___y_2475_);
return v___x_2529_;
}
case 2:
{
lean_object* v___x_2530_; 
lean_dec(v_stx_2464_);
lean_inc(v_declName_2466_);
v___x_2530_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_2466_, v___x_2470_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2531_);
lean_dec_ref_known(v___x_2530_, 1);
if (lean_obj_tag(v_a_2531_) == 1)
{
lean_object* v_val_2532_; lean_object* v_ctors_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
lean_dec(v_attrName_2471_);
lean_dec(v_declName_2466_);
v_val_2532_ = lean_ctor_get(v_a_2531_, 0);
lean_inc(v_val_2532_);
lean_dec_ref_known(v_a_2531_, 1);
v_ctors_2533_ = lean_ctor_get(v_val_2532_, 4);
lean_inc(v_ctors_2533_);
lean_dec(v_val_2532_);
v___x_2534_ = lean_box(0);
v___x_2535_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2465_, v_attrKind_2467_, v_showInfo_2468_, v_minIndexable_2469_, v_ctors_2533_, v___x_2534_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
lean_dec(v_ctors_2533_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2542_ == 0)
{
lean_object* v_unused_2543_; 
v_unused_2543_ = lean_ctor_get(v___x_2535_, 0);
lean_dec(v_unused_2543_);
v___x_2537_ = v___x_2535_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_dec(v___x_2535_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 0, v___x_2534_);
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2534_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
else
{
return v___x_2535_;
}
}
else
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
lean_dec(v_a_2531_);
lean_dec_ref(v_ext_2465_);
v___x_2544_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4);
v___x_2545_ = l_Lean_MessageData_ofName(v_attrName_2471_);
v___x_2546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2544_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
v___x_2547_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6);
v___x_2548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2546_);
lean_ctor_set(v___x_2548_, 1, v___x_2547_);
v___x_2549_ = l_Lean_MessageData_ofConstName(v_declName_2466_, v___x_2470_);
v___x_2550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2548_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
v___x_2551_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8);
v___x_2552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2550_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2552_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2553_;
}
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_dec(v_attrName_2471_);
lean_dec(v_declName_2466_);
lean_dec_ref(v_ext_2465_);
v_a_2554_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2530_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2530_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
case 3:
{
lean_object* v___x_2562_; 
lean_dec(v_attrName_2471_);
lean_inc(v_declName_2466_);
v___x_2562_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_2466_, v___x_2470_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
if (lean_obj_tag(v_a_2563_) == 1)
{
lean_object* v_val_2564_; lean_object* v___x_2565_; 
lean_dec(v_declName_2466_);
lean_dec(v_stx_2464_);
v_val_2564_ = lean_ctor_get(v_a_2563_, 0);
lean_inc_n(v_val_2564_, 2);
lean_dec_ref_known(v_a_2563_, 1);
lean_inc_ref(v_ext_2465_);
v___x_2565_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2465_, v_val_2564_, v___x_2470_, v_attrKind_2467_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v___x_2566_; 
lean_dec_ref_known(v___x_2565_, 1);
v___x_2566_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_2564_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2587_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2569_ = v___x_2566_;
v_isShared_2570_ = v_isSharedCheck_2587_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2566_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2587_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
if (lean_obj_tag(v_a_2567_) == 1)
{
lean_object* v_val_2571_; lean_object* v_ctors_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
lean_del_object(v___x_2569_);
v_val_2571_ = lean_ctor_get(v_a_2567_, 0);
lean_inc(v_val_2571_);
lean_dec_ref_known(v_a_2567_, 1);
v_ctors_2572_ = lean_ctor_get(v_val_2571_, 4);
lean_inc(v_ctors_2572_);
lean_dec(v_val_2571_);
v___x_2573_ = lean_box(0);
v___x_2574_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2465_, v_attrKind_2467_, v_showInfo_2468_, v_minIndexable_2469_, v_ctors_2572_, v___x_2573_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
lean_dec(v_ctors_2572_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2581_ == 0)
{
lean_object* v_unused_2582_; 
v_unused_2582_ = lean_ctor_get(v___x_2574_, 0);
lean_dec(v_unused_2582_);
v___x_2576_ = v___x_2574_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_dec(v___x_2574_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v___x_2573_);
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2573_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
else
{
return v___x_2574_;
}
}
else
{
lean_object* v___x_2583_; lean_object* v___x_2585_; 
lean_dec(v_a_2567_);
lean_dec_ref(v_ext_2465_);
v___x_2583_ = lean_box(0);
if (v_isShared_2570_ == 0)
{
lean_ctor_set(v___x_2569_, 0, v___x_2583_);
v___x_2585_ = v___x_2569_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_dec_ref(v_ext_2465_);
v_a_2588_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2566_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2566_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
else
{
lean_dec(v_val_2564_);
lean_dec_ref(v_ext_2465_);
return v___x_2565_;
}
}
else
{
lean_object* v___x_2596_; 
lean_dec(v_a_2563_);
v___x_2596_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2475_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v___x_2598_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_a_2597_);
lean_dec_ref_known(v___x_2596_, 1);
v___x_2598_ = l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(v_ext_2465_, v_stx_2464_, v_declName_2466_, v_attrKind_2467_, v_a_2597_, v_minIndexable_2469_, v_showInfo_2468_, v___x_2470_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2598_;
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
lean_dec(v_declName_2466_);
lean_dec_ref(v_ext_2465_);
lean_dec(v_stx_2464_);
v_a_2599_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2596_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2596_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec(v_declName_2466_);
lean_dec_ref(v_ext_2465_);
lean_dec(v_stx_2464_);
v_a_2607_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2562_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2562_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
case 4:
{
lean_object* v___x_2615_; 
lean_dec(v_attrName_2471_);
lean_dec(v_stx_2464_);
v___x_2615_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_2465_, v_declName_2466_, v_attrKind_2467_, v___y_2474_, v___y_2475_);
return v___x_2615_;
}
case 5:
{
lean_object* v_prio_2616_; lean_object* v___x_2617_; uint8_t v___x_2618_; 
lean_dec_ref(v_ext_2465_);
lean_dec(v_stx_2464_);
v_prio_2616_ = lean_ctor_get(v_a_2514_, 0);
lean_inc(v_prio_2616_);
lean_dec_ref_known(v_a_2514_, 1);
v___x_2617_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10));
v___x_2618_ = lean_name_eq(v_attrName_2471_, v___x_2617_);
lean_dec(v_attrName_2471_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; lean_object* v___x_2620_; 
lean_dec(v_prio_2616_);
lean_dec(v_declName_2466_);
v___x_2619_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12);
v___x_2620_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2619_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2620_;
}
else
{
lean_object* v___x_2621_; 
v___x_2621_ = l_Lean_Meta_Grind_addSymbolPriorityAttr(v_declName_2466_, v_attrKind_2467_, v_prio_2616_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2621_;
}
}
case 6:
{
lean_object* v___x_2622_; 
lean_dec(v_attrName_2471_);
lean_dec(v_stx_2464_);
v___x_2622_ = l_Lean_Meta_Grind_Extension_addInjectiveAttr(v_ext_2465_, v_declName_2466_, v_attrKind_2467_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2622_;
}
case 7:
{
lean_object* v___x_2623_; 
lean_dec(v_attrName_2471_);
lean_dec(v_stx_2464_);
v___x_2623_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_2465_, v_declName_2466_, v_attrKind_2467_, v___y_2474_, v___y_2475_);
return v___x_2623_;
}
case 8:
{
uint8_t v_post_2624_; uint8_t v_inv_2625_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___x_2634_; uint8_t v___x_2635_; 
lean_dec_ref(v_ext_2465_);
lean_dec(v_stx_2464_);
v_post_2624_ = lean_ctor_get_uint8(v_a_2514_, 0);
v_inv_2625_ = lean_ctor_get_uint8(v_a_2514_, 1);
lean_dec_ref_known(v_a_2514_, 0);
v___x_2634_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10));
v___x_2635_ = lean_name_eq(v_attrName_2471_, v___x_2634_);
lean_dec(v_attrName_2471_);
if (v___x_2635_ == 0)
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
lean_dec(v_declName_2466_);
v___x_2636_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14);
v___x_2637_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2636_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2637_;
}
else
{
v___y_2627_ = v___y_2472_;
v___y_2628_ = v___y_2473_;
v___y_2629_ = v___y_2474_;
v___y_2630_ = v___y_2475_;
goto v___jp_2626_;
}
v___jp_2626_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2631_ = l_Lean_Meta_Grind_normExt;
v___x_2632_ = lean_unsigned_to_nat(1000u);
v___x_2633_ = l_Lean_Meta_addSimpTheorem(v___x_2631_, v_declName_2466_, v_post_2624_, v_inv_2625_, v_attrKind_2467_, v___x_2632_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
return v___x_2633_;
}
}
case 9:
{
lean_object* v___x_2638_; uint8_t v___x_2639_; 
lean_dec_ref(v_ext_2465_);
lean_dec(v_stx_2464_);
v___x_2638_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10));
v___x_2639_ = lean_name_eq(v_attrName_2471_, v___x_2638_);
lean_dec(v_attrName_2471_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
lean_dec(v_declName_2466_);
v___x_2640_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16);
v___x_2641_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2640_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2641_;
}
else
{
v___y_2478_ = v___y_2472_;
v___y_2479_ = v___y_2473_;
v___y_2480_ = v___y_2474_;
v___y_2481_ = v___y_2475_;
goto v___jp_2477_;
}
}
default: 
{
lean_object* v___x_2642_; uint8_t v___x_2643_; 
lean_dec_ref(v_ext_2465_);
lean_dec(v_stx_2464_);
v___x_2642_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10));
v___x_2643_ = lean_name_eq(v_attrName_2471_, v___x_2642_);
lean_dec(v_attrName_2471_);
if (v___x_2643_ == 0)
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
lean_dec(v_declName_2466_);
v___x_2644_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18);
v___x_2645_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2644_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2645_;
}
else
{
v___y_2506_ = v___y_2472_;
v___y_2507_ = v___y_2473_;
v___y_2508_ = v___y_2474_;
v___y_2509_ = v___y_2475_;
goto v___jp_2505_;
}
}
}
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec(v_attrName_2471_);
lean_dec(v_declName_2466_);
lean_dec_ref(v_ext_2465_);
lean_dec(v_stx_2464_);
v_a_2646_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2513_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2513_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
v___jp_2477_:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2482_ = l_Lean_Meta_Grind_normExt;
v___x_2483_ = lean_unsigned_to_nat(1000u);
v___x_2484_ = l_Lean_Meta_addDeclToUnfold(v___x_2482_, v_declName_2466_, v___x_2470_, v___x_2470_, v___x_2483_, v_attrKind_2467_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2496_; 
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2487_ = v___x_2484_;
v_isShared_2488_ = v_isSharedCheck_2496_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2484_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2496_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
uint8_t v___x_2489_; 
v___x_2489_ = lean_unbox(v_a_2485_);
lean_dec(v_a_2485_);
if (v___x_2489_ == 0)
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
lean_del_object(v___x_2487_);
v___x_2490_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1);
v___x_2491_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2490_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
return v___x_2491_;
}
else
{
lean_object* v___x_2492_; lean_object* v___x_2494_; 
v___x_2492_ = lean_box(0);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 0, v___x_2492_);
v___x_2494_ = v___x_2487_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2492_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
v_a_2497_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2484_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2484_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
v___jp_2505_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = l_Lean_Meta_Grind_homoExt;
v___x_2511_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2));
v___x_2512_ = l_Lean_Meta_Sym_Simp_addSymSimpDecl(v___x_2510_, v___x_2511_, v_declName_2466_, v_attrKind_2467_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
return v___x_2512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object* v_stx_2654_, lean_object* v_ext_2655_, lean_object* v_declName_2656_, lean_object* v_attrKind_2657_, lean_object* v_showInfo_2658_, lean_object* v_minIndexable_2659_, lean_object* v___x_2660_, lean_object* v_attrName_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
uint8_t v_attrKind_boxed_2667_; uint8_t v_showInfo_boxed_2668_; uint8_t v_minIndexable_boxed_2669_; uint8_t v___x_15606__boxed_2670_; lean_object* v_res_2671_; 
v_attrKind_boxed_2667_ = lean_unbox(v_attrKind_2657_);
v_showInfo_boxed_2668_ = lean_unbox(v_showInfo_2658_);
v_minIndexable_boxed_2669_ = lean_unbox(v_minIndexable_2659_);
v___x_15606__boxed_2670_ = lean_unbox(v___x_2660_);
v_res_2671_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(v_stx_2654_, v_ext_2655_, v_declName_2656_, v_attrKind_boxed_2667_, v_showInfo_boxed_2668_, v_minIndexable_boxed_2669_, v___x_15606__boxed_2670_, v_attrName_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
return v_res_2671_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2672_; double v___x_2673_; 
v___x_2672_ = lean_unsigned_to_nat(0u);
v___x_2673_ = lean_float_of_nat(v___x_2672_);
return v___x_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(lean_object* v_cls_2677_, lean_object* v_msg_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v_ref_2684_; lean_object* v___x_2685_; lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2730_; 
v_ref_2684_ = lean_ctor_get(v___y_2681_, 5);
v___x_2685_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2688_ = v___x_2685_;
v_isShared_2689_ = v_isSharedCheck_2730_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2730_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; lean_object* v_traceState_2691_; lean_object* v_env_2692_; lean_object* v_nextMacroScope_2693_; lean_object* v_ngen_2694_; lean_object* v_auxDeclNGen_2695_; lean_object* v_cache_2696_; lean_object* v_messages_2697_; lean_object* v_infoState_2698_; lean_object* v_snapshotTasks_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2729_; 
v___x_2690_ = lean_st_ref_take(v___y_2682_);
v_traceState_2691_ = lean_ctor_get(v___x_2690_, 4);
v_env_2692_ = lean_ctor_get(v___x_2690_, 0);
v_nextMacroScope_2693_ = lean_ctor_get(v___x_2690_, 1);
v_ngen_2694_ = lean_ctor_get(v___x_2690_, 2);
v_auxDeclNGen_2695_ = lean_ctor_get(v___x_2690_, 3);
v_cache_2696_ = lean_ctor_get(v___x_2690_, 5);
v_messages_2697_ = lean_ctor_get(v___x_2690_, 6);
v_infoState_2698_ = lean_ctor_get(v___x_2690_, 7);
v_snapshotTasks_2699_ = lean_ctor_get(v___x_2690_, 8);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2701_ = v___x_2690_;
v_isShared_2702_ = v_isSharedCheck_2729_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_snapshotTasks_2699_);
lean_inc(v_infoState_2698_);
lean_inc(v_messages_2697_);
lean_inc(v_cache_2696_);
lean_inc(v_traceState_2691_);
lean_inc(v_auxDeclNGen_2695_);
lean_inc(v_ngen_2694_);
lean_inc(v_nextMacroScope_2693_);
lean_inc(v_env_2692_);
lean_dec(v___x_2690_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2729_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
uint64_t v_tid_2703_; lean_object* v_traces_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2728_; 
v_tid_2703_ = lean_ctor_get_uint64(v_traceState_2691_, sizeof(void*)*1);
v_traces_2704_ = lean_ctor_get(v_traceState_2691_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v_traceState_2691_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2706_ = v_traceState_2691_;
v_isShared_2707_ = v_isSharedCheck_2728_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_traces_2704_);
lean_dec(v_traceState_2691_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2728_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2708_; double v___x_2709_; uint8_t v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2708_ = lean_box(0);
v___x_2709_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_2710_ = 0;
v___x_2711_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2712_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2712_, 0, v_cls_2677_);
lean_ctor_set(v___x_2712_, 1, v___x_2708_);
lean_ctor_set(v___x_2712_, 2, v___x_2711_);
lean_ctor_set_float(v___x_2712_, sizeof(void*)*3, v___x_2709_);
lean_ctor_set_float(v___x_2712_, sizeof(void*)*3 + 8, v___x_2709_);
lean_ctor_set_uint8(v___x_2712_, sizeof(void*)*3 + 16, v___x_2710_);
v___x_2713_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_2714_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2712_);
lean_ctor_set(v___x_2714_, 1, v_a_2686_);
lean_ctor_set(v___x_2714_, 2, v___x_2713_);
lean_inc(v_ref_2684_);
v___x_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2715_, 0, v_ref_2684_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = l_Lean_PersistentArray_push___redArg(v_traces_2704_, v___x_2715_);
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 0, v___x_2716_);
v___x_2718_ = v___x_2706_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2716_);
lean_ctor_set_uint64(v_reuseFailAlloc_2727_, sizeof(void*)*1, v_tid_2703_);
v___x_2718_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
lean_object* v___x_2720_; 
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 4, v___x_2718_);
v___x_2720_ = v___x_2701_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_env_2692_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_nextMacroScope_2693_);
lean_ctor_set(v_reuseFailAlloc_2726_, 2, v_ngen_2694_);
lean_ctor_set(v_reuseFailAlloc_2726_, 3, v_auxDeclNGen_2695_);
lean_ctor_set(v_reuseFailAlloc_2726_, 4, v___x_2718_);
lean_ctor_set(v_reuseFailAlloc_2726_, 5, v_cache_2696_);
lean_ctor_set(v_reuseFailAlloc_2726_, 6, v_messages_2697_);
lean_ctor_set(v_reuseFailAlloc_2726_, 7, v_infoState_2698_);
lean_ctor_set(v_reuseFailAlloc_2726_, 8, v_snapshotTasks_2699_);
v___x_2720_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2721_ = lean_st_ref_set(v___y_2682_, v___x_2720_);
v___x_2722_ = lean_box(0);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2722_);
v___x_2724_ = v___x_2688_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___boxed(lean_object* v_cls_2731_, lean_object* v_msg_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2731_, v_msg_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
return v_res_2738_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(lean_object* v_keys_2739_, lean_object* v_i_2740_, lean_object* v_k_2741_){
_start:
{
lean_object* v___x_2742_; uint8_t v___x_2743_; 
v___x_2742_ = lean_array_get_size(v_keys_2739_);
v___x_2743_ = lean_nat_dec_lt(v_i_2740_, v___x_2742_);
if (v___x_2743_ == 0)
{
lean_dec(v_i_2740_);
return v___x_2743_;
}
else
{
lean_object* v_k_x27_2744_; uint8_t v___x_2745_; 
v_k_x27_2744_ = lean_array_fget_borrowed(v_keys_2739_, v_i_2740_);
v___x_2745_ = l_Lean_instBEqExtraModUse_beq(v_k_2741_, v_k_x27_2744_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2746_ = lean_unsigned_to_nat(1u);
v___x_2747_ = lean_nat_add(v_i_2740_, v___x_2746_);
lean_dec(v_i_2740_);
v_i_2740_ = v___x_2747_;
goto _start;
}
else
{
lean_dec(v_i_2740_);
return v___x_2745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_keys_2749_, lean_object* v_i_2750_, lean_object* v_k_2751_){
_start:
{
uint8_t v_res_2752_; lean_object* v_r_2753_; 
v_res_2752_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_2749_, v_i_2750_, v_k_2751_);
lean_dec_ref(v_k_2751_);
lean_dec_ref(v_keys_2749_);
v_r_2753_ = lean_box(v_res_2752_);
return v_r_2753_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_x_2754_, size_t v_x_2755_, lean_object* v_x_2756_){
_start:
{
if (lean_obj_tag(v_x_2754_) == 0)
{
lean_object* v_es_2757_; lean_object* v___x_2758_; size_t v___x_2759_; size_t v___x_2760_; lean_object* v_j_2761_; lean_object* v___x_2762_; 
v_es_2757_ = lean_ctor_get(v_x_2754_, 0);
v___x_2758_ = lean_box(2);
v___x_2759_ = ((size_t)31ULL);
v___x_2760_ = lean_usize_land(v_x_2755_, v___x_2759_);
v_j_2761_ = lean_usize_to_nat(v___x_2760_);
v___x_2762_ = lean_array_get_borrowed(v___x_2758_, v_es_2757_, v_j_2761_);
lean_dec(v_j_2761_);
switch(lean_obj_tag(v___x_2762_))
{
case 0:
{
lean_object* v_key_2763_; uint8_t v___x_2764_; 
v_key_2763_ = lean_ctor_get(v___x_2762_, 0);
v___x_2764_ = l_Lean_instBEqExtraModUse_beq(v_x_2756_, v_key_2763_);
return v___x_2764_;
}
case 1:
{
lean_object* v_node_2765_; size_t v___x_2766_; size_t v___x_2767_; 
v_node_2765_ = lean_ctor_get(v___x_2762_, 0);
v___x_2766_ = ((size_t)5ULL);
v___x_2767_ = lean_usize_shift_right(v_x_2755_, v___x_2766_);
v_x_2754_ = v_node_2765_;
v_x_2755_ = v___x_2767_;
goto _start;
}
default: 
{
uint8_t v___x_2769_; 
v___x_2769_ = 0;
return v___x_2769_;
}
}
}
else
{
lean_object* v_ks_2770_; lean_object* v___x_2771_; uint8_t v___x_2772_; 
v_ks_2770_ = lean_ctor_get(v_x_2754_, 0);
v___x_2771_ = lean_unsigned_to_nat(0u);
v___x_2772_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_ks_2770_, v___x_2771_, v_x_2756_);
return v___x_2772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_x_2773_, lean_object* v_x_2774_, lean_object* v_x_2775_){
_start:
{
size_t v_x_16130__boxed_2776_; uint8_t v_res_2777_; lean_object* v_r_2778_; 
v_x_16130__boxed_2776_ = lean_unbox_usize(v_x_2774_);
lean_dec(v_x_2774_);
v_res_2777_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2773_, v_x_16130__boxed_2776_, v_x_2775_);
lean_dec_ref(v_x_2775_);
lean_dec_ref(v_x_2773_);
v_r_2778_ = lean_box(v_res_2777_);
return v_r_2778_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(lean_object* v_x_2779_, lean_object* v_x_2780_){
_start:
{
uint64_t v___x_2781_; size_t v___x_2782_; uint8_t v___x_2783_; 
v___x_2781_ = l_Lean_instHashableExtraModUse_hash(v_x_2780_);
v___x_2782_ = lean_uint64_to_usize(v___x_2781_);
v___x_2783_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2779_, v___x_2782_, v_x_2780_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_2784_, lean_object* v_x_2785_){
_start:
{
uint8_t v_res_2786_; lean_object* v_r_2787_; 
v_res_2786_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_2784_, v_x_2785_);
lean_dec_ref(v_x_2785_);
lean_dec_ref(v_x_2784_);
v_r_2787_ = lean_box(v_res_2786_);
return v_r_2787_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2790_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1));
v___x_2791_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0));
v___x_2792_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2791_, v___x_2790_);
return v___x_2792_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2797_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5));
v___x_2798_ = l_Lean_stringToMessageData(v___x_2797_);
return v___x_2798_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8(void){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7));
v___x_2801_ = l_Lean_stringToMessageData(v___x_2800_);
return v___x_2801_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9(void){
_start:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2803_ = l_Lean_stringToMessageData(v___x_2802_);
return v___x_2803_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v_cls_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v_cls_2807_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_2808_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11));
v___x_2809_ = l_Lean_Name_append(v___x_2808_, v_cls_2807_);
return v___x_2809_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13));
v___x_2812_ = l_Lean_stringToMessageData(v___x_2811_);
return v___x_2812_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16(void){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15));
v___x_2815_ = l_Lean_stringToMessageData(v___x_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object* v_mod_2820_, uint8_t v_isMeta_2821_, lean_object* v_hint_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v___x_2828_; lean_object* v_env_2829_; uint8_t v_isExporting_2830_; lean_object* v___x_2831_; lean_object* v_env_2832_; lean_object* v___x_2833_; lean_object* v_entry_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___x_2880_; uint8_t v___x_2881_; 
v___x_2828_ = lean_st_ref_get(v___y_2826_);
v_env_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc_ref(v_env_2829_);
lean_dec(v___x_2828_);
v_isExporting_2830_ = lean_ctor_get_uint8(v_env_2829_, sizeof(void*)*8);
lean_dec_ref(v_env_2829_);
v___x_2831_ = lean_st_ref_get(v___y_2826_);
v_env_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc_ref(v_env_2832_);
lean_dec(v___x_2831_);
v___x_2833_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2);
lean_inc(v_mod_2820_);
v_entry_2834_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2834_, 0, v_mod_2820_);
lean_ctor_set_uint8(v_entry_2834_, sizeof(void*)*1, v_isExporting_2830_);
lean_ctor_set_uint8(v_entry_2834_, sizeof(void*)*1 + 1, v_isMeta_2821_);
v___x_2835_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2836_ = lean_box(1);
v___x_2837_ = lean_box(0);
v___x_2880_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2833_, v___x_2835_, v_env_2832_, v___x_2836_, v___x_2837_);
v___x_2881_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_2880_, v_entry_2834_);
lean_dec(v___x_2880_);
if (v___x_2881_ == 0)
{
lean_object* v_options_2882_; uint8_t v_hasTrace_2883_; 
v_options_2882_ = lean_ctor_get(v___y_2825_, 2);
v_hasTrace_2883_ = lean_ctor_get_uint8(v_options_2882_, sizeof(void*)*1);
if (v_hasTrace_2883_ == 0)
{
lean_dec(v_hint_2822_);
lean_dec(v_mod_2820_);
v___y_2839_ = v___y_2824_;
v___y_2840_ = v___y_2826_;
goto v___jp_2838_;
}
else
{
lean_object* v_inheritedTraceOptions_2884_; lean_object* v_cls_2885_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___x_2905_; uint8_t v___x_2906_; 
v_inheritedTraceOptions_2884_ = lean_ctor_get(v___y_2825_, 13);
v_cls_2885_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_2905_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
v___x_2906_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2884_, v_options_2882_, v___x_2905_);
if (v___x_2906_ == 0)
{
lean_dec(v_hint_2822_);
lean_dec(v_mod_2820_);
v___y_2839_ = v___y_2824_;
v___y_2840_ = v___y_2826_;
goto v___jp_2838_;
}
else
{
lean_object* v___x_2907_; lean_object* v___y_2909_; 
v___x_2907_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
if (v_isExporting_2830_ == 0)
{
lean_object* v___x_2916_; 
v___x_2916_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19));
v___y_2909_ = v___x_2916_;
goto v___jp_2908_;
}
else
{
lean_object* v___x_2917_; 
v___x_2917_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20));
v___y_2909_ = v___x_2917_;
goto v___jp_2908_;
}
v___jp_2908_:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
lean_inc_ref(v___y_2909_);
v___x_2910_ = l_Lean_stringToMessageData(v___y_2909_);
v___x_2911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2907_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
v___x_2912_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16);
v___x_2913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2911_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
if (v_isMeta_2821_ == 0)
{
lean_object* v___x_2914_; 
v___x_2914_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_2892_ = v___x_2913_;
v___y_2893_ = v___x_2914_;
goto v___jp_2891_;
}
else
{
lean_object* v___x_2915_; 
v___x_2915_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_2892_ = v___x_2913_;
v___y_2893_ = v___x_2915_;
goto v___jp_2891_;
}
}
}
v___jp_2886_:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___y_2887_);
lean_ctor_set(v___x_2889_, 1, v___y_2888_);
v___x_2890_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2885_, v___x_2889_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_dec_ref_known(v___x_2890_, 1);
v___y_2839_ = v___y_2824_;
v___y_2840_ = v___y_2826_;
goto v___jp_2838_;
}
else
{
lean_dec_ref_known(v_entry_2834_, 1);
return v___x_2890_;
}
}
v___jp_2891_:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; uint8_t v___x_2900_; 
lean_inc_ref(v___y_2893_);
v___x_2894_ = l_Lean_stringToMessageData(v___y_2893_);
v___x_2895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___y_2892_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
v___x_2896_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_2897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2895_);
lean_ctor_set(v___x_2897_, 1, v___x_2896_);
v___x_2898_ = l_Lean_MessageData_ofName(v_mod_2820_);
v___x_2899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2897_);
lean_ctor_set(v___x_2899_, 1, v___x_2898_);
v___x_2900_ = l_Lean_Name_isAnonymous(v_hint_2822_);
if (v___x_2900_ == 0)
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2901_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8);
v___x_2902_ = l_Lean_MessageData_ofName(v_hint_2822_);
v___x_2903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2901_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
v___y_2887_ = v___x_2899_;
v___y_2888_ = v___x_2903_;
goto v___jp_2886_;
}
else
{
lean_object* v___x_2904_; 
lean_dec(v_hint_2822_);
v___x_2904_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9);
v___y_2887_ = v___x_2899_;
v___y_2888_ = v___x_2904_;
goto v___jp_2886_;
}
}
}
}
else
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
lean_dec_ref_known(v_entry_2834_, 1);
lean_dec(v_hint_2822_);
lean_dec(v_mod_2820_);
v___x_2918_ = lean_box(0);
v___x_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
return v___x_2919_;
}
v___jp_2838_:
{
lean_object* v___x_2841_; lean_object* v_toEnvExtension_2842_; lean_object* v_env_2843_; lean_object* v_nextMacroScope_2844_; lean_object* v_ngen_2845_; lean_object* v_auxDeclNGen_2846_; lean_object* v_traceState_2847_; lean_object* v_messages_2848_; lean_object* v_infoState_2849_; lean_object* v_snapshotTasks_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2878_; 
v___x_2841_ = lean_st_ref_take(v___y_2840_);
v_toEnvExtension_2842_ = lean_ctor_get(v___x_2835_, 0);
v_env_2843_ = lean_ctor_get(v___x_2841_, 0);
v_nextMacroScope_2844_ = lean_ctor_get(v___x_2841_, 1);
v_ngen_2845_ = lean_ctor_get(v___x_2841_, 2);
v_auxDeclNGen_2846_ = lean_ctor_get(v___x_2841_, 3);
v_traceState_2847_ = lean_ctor_get(v___x_2841_, 4);
v_messages_2848_ = lean_ctor_get(v___x_2841_, 6);
v_infoState_2849_ = lean_ctor_get(v___x_2841_, 7);
v_snapshotTasks_2850_ = lean_ctor_get(v___x_2841_, 8);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2878_ == 0)
{
lean_object* v_unused_2879_; 
v_unused_2879_ = lean_ctor_get(v___x_2841_, 5);
lean_dec(v_unused_2879_);
v___x_2852_ = v___x_2841_;
v_isShared_2853_ = v_isSharedCheck_2878_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_snapshotTasks_2850_);
lean_inc(v_infoState_2849_);
lean_inc(v_messages_2848_);
lean_inc(v_traceState_2847_);
lean_inc(v_auxDeclNGen_2846_);
lean_inc(v_ngen_2845_);
lean_inc(v_nextMacroScope_2844_);
lean_inc(v_env_2843_);
lean_dec(v___x_2841_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2878_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v_asyncMode_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2858_; 
v_asyncMode_2854_ = lean_ctor_get(v_toEnvExtension_2842_, 2);
v___x_2855_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2835_, v_env_2843_, v_entry_2834_, v_asyncMode_2854_, v___x_2837_);
v___x_2856_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 5, v___x_2856_);
lean_ctor_set(v___x_2852_, 0, v___x_2855_);
v___x_2858_ = v___x_2852_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2855_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_nextMacroScope_2844_);
lean_ctor_set(v_reuseFailAlloc_2877_, 2, v_ngen_2845_);
lean_ctor_set(v_reuseFailAlloc_2877_, 3, v_auxDeclNGen_2846_);
lean_ctor_set(v_reuseFailAlloc_2877_, 4, v_traceState_2847_);
lean_ctor_set(v_reuseFailAlloc_2877_, 5, v___x_2856_);
lean_ctor_set(v_reuseFailAlloc_2877_, 6, v_messages_2848_);
lean_ctor_set(v_reuseFailAlloc_2877_, 7, v_infoState_2849_);
lean_ctor_set(v_reuseFailAlloc_2877_, 8, v_snapshotTasks_2850_);
v___x_2858_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v_mctx_2861_; lean_object* v_zetaDeltaFVarIds_2862_; lean_object* v_postponed_2863_; lean_object* v_diag_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2875_; 
v___x_2859_ = lean_st_ref_set(v___y_2840_, v___x_2858_);
v___x_2860_ = lean_st_ref_take(v___y_2839_);
v_mctx_2861_ = lean_ctor_get(v___x_2860_, 0);
v_zetaDeltaFVarIds_2862_ = lean_ctor_get(v___x_2860_, 2);
v_postponed_2863_ = lean_ctor_get(v___x_2860_, 3);
v_diag_2864_ = lean_ctor_get(v___x_2860_, 4);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2875_ == 0)
{
lean_object* v_unused_2876_; 
v_unused_2876_ = lean_ctor_get(v___x_2860_, 1);
lean_dec(v_unused_2876_);
v___x_2866_ = v___x_2860_;
v_isShared_2867_ = v_isSharedCheck_2875_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_diag_2864_);
lean_inc(v_postponed_2863_);
lean_inc(v_zetaDeltaFVarIds_2862_);
lean_inc(v_mctx_2861_);
lean_dec(v___x_2860_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2875_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2868_; lean_object* v___x_2870_; 
v___x_2868_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 1, v___x_2868_);
v___x_2870_ = v___x_2866_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_mctx_2861_);
lean_ctor_set(v_reuseFailAlloc_2874_, 1, v___x_2868_);
lean_ctor_set(v_reuseFailAlloc_2874_, 2, v_zetaDeltaFVarIds_2862_);
lean_ctor_set(v_reuseFailAlloc_2874_, 3, v_postponed_2863_);
lean_ctor_set(v_reuseFailAlloc_2874_, 4, v_diag_2864_);
v___x_2870_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2871_ = lean_st_ref_set(v___y_2839_, v___x_2870_);
v___x_2872_ = lean_box(0);
v___x_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
return v___x_2873_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object* v_mod_2920_, lean_object* v_isMeta_2921_, lean_object* v_hint_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
uint8_t v_isMeta_boxed_2928_; lean_object* v_res_2929_; 
v_isMeta_boxed_2928_ = lean_unbox(v_isMeta_2921_);
v_res_2929_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_mod_2920_, v_isMeta_boxed_2928_, v_hint_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(lean_object* v_a_2930_, lean_object* v_x_2931_){
_start:
{
if (lean_obj_tag(v_x_2931_) == 0)
{
lean_object* v___x_2932_; 
v___x_2932_ = lean_box(0);
return v___x_2932_;
}
else
{
lean_object* v_key_2933_; lean_object* v_value_2934_; lean_object* v_tail_2935_; uint8_t v___x_2936_; 
v_key_2933_ = lean_ctor_get(v_x_2931_, 0);
v_value_2934_ = lean_ctor_get(v_x_2931_, 1);
v_tail_2935_ = lean_ctor_get(v_x_2931_, 2);
v___x_2936_ = lean_name_eq(v_key_2933_, v_a_2930_);
if (v___x_2936_ == 0)
{
v_x_2931_ = v_tail_2935_;
goto _start;
}
else
{
lean_object* v___x_2938_; 
lean_inc(v_value_2934_);
v___x_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2938_, 0, v_value_2934_);
return v___x_2938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_a_2939_, lean_object* v_x_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_2939_, v_x_2940_);
lean_dec(v_x_2940_);
lean_dec(v_a_2939_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(lean_object* v_m_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v_buckets_2944_; lean_object* v___x_2945_; uint64_t v___y_2947_; 
v_buckets_2944_ = lean_ctor_get(v_m_2942_, 1);
v___x_2945_ = lean_array_get_size(v_buckets_2944_);
if (lean_obj_tag(v_a_2943_) == 0)
{
uint64_t v___x_2961_; 
v___x_2961_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_2947_ = v___x_2961_;
goto v___jp_2946_;
}
else
{
uint64_t v_hash_2962_; 
v_hash_2962_ = lean_ctor_get_uint64(v_a_2943_, sizeof(void*)*2);
v___y_2947_ = v_hash_2962_;
goto v___jp_2946_;
}
v___jp_2946_:
{
uint64_t v___x_2948_; uint64_t v___x_2949_; uint64_t v_fold_2950_; uint64_t v___x_2951_; uint64_t v___x_2952_; uint64_t v___x_2953_; size_t v___x_2954_; size_t v___x_2955_; size_t v___x_2956_; size_t v___x_2957_; size_t v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2948_ = 32ULL;
v___x_2949_ = lean_uint64_shift_right(v___y_2947_, v___x_2948_);
v_fold_2950_ = lean_uint64_xor(v___y_2947_, v___x_2949_);
v___x_2951_ = 16ULL;
v___x_2952_ = lean_uint64_shift_right(v_fold_2950_, v___x_2951_);
v___x_2953_ = lean_uint64_xor(v_fold_2950_, v___x_2952_);
v___x_2954_ = lean_uint64_to_usize(v___x_2953_);
v___x_2955_ = lean_usize_of_nat(v___x_2945_);
v___x_2956_ = ((size_t)1ULL);
v___x_2957_ = lean_usize_sub(v___x_2955_, v___x_2956_);
v___x_2958_ = lean_usize_land(v___x_2954_, v___x_2957_);
v___x_2959_ = lean_array_uget_borrowed(v_buckets_2944_, v___x_2958_);
v___x_2960_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_2943_, v___x_2959_);
return v___x_2960_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg___boxed(lean_object* v_m_2963_, lean_object* v_a_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_2963_, v_a_2964_);
lean_dec(v_a_2964_);
lean_dec_ref(v_m_2963_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object* v___x_2966_, lean_object* v_declName_2967_, lean_object* v_as_2968_, size_t v_sz_2969_, size_t v_i_2970_, lean_object* v_b_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
uint8_t v___x_2977_; 
v___x_2977_ = lean_usize_dec_lt(v_i_2970_, v_sz_2969_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; 
lean_dec(v_declName_2967_);
v___x_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2978_, 0, v_b_2971_);
return v___x_2978_;
}
else
{
lean_object* v___x_2979_; lean_object* v_modules_2980_; lean_object* v___x_2981_; lean_object* v_a_2982_; lean_object* v___x_2983_; lean_object* v_toImport_2984_; lean_object* v_module_2985_; uint8_t v___x_2986_; lean_object* v___x_2987_; 
v___x_2979_ = l_Lean_Environment_header(v___x_2966_);
v_modules_2980_ = lean_ctor_get(v___x_2979_, 3);
lean_inc_ref(v_modules_2980_);
lean_dec_ref(v___x_2979_);
v___x_2981_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2982_ = lean_array_uget_borrowed(v_as_2968_, v_i_2970_);
v___x_2983_ = lean_array_get(v___x_2981_, v_modules_2980_, v_a_2982_);
lean_dec_ref(v_modules_2980_);
v_toImport_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc_ref(v_toImport_2984_);
lean_dec(v___x_2983_);
v_module_2985_ = lean_ctor_get(v_toImport_2984_, 0);
lean_inc(v_module_2985_);
lean_dec_ref(v_toImport_2984_);
v___x_2986_ = 0;
lean_inc(v_declName_2967_);
v___x_2987_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_2985_, v___x_2986_, v_declName_2967_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v___x_2988_; size_t v___x_2989_; size_t v___x_2990_; 
lean_dec_ref_known(v___x_2987_, 1);
v___x_2988_ = lean_box(0);
v___x_2989_ = ((size_t)1ULL);
v___x_2990_ = lean_usize_add(v_i_2970_, v___x_2989_);
v_i_2970_ = v___x_2990_;
v_b_2971_ = v___x_2988_;
goto _start;
}
else
{
lean_dec(v_declName_2967_);
return v___x_2987_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object* v___x_2992_, lean_object* v_declName_2993_, lean_object* v_as_2994_, lean_object* v_sz_2995_, lean_object* v_i_2996_, lean_object* v_b_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
size_t v_sz_boxed_3003_; size_t v_i_boxed_3004_; lean_object* v_res_3005_; 
v_sz_boxed_3003_ = lean_unbox_usize(v_sz_2995_);
lean_dec(v_sz_2995_);
v_i_boxed_3004_ = lean_unbox_usize(v_i_2996_);
lean_dec(v_i_2996_);
v_res_3005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v___x_2992_, v_declName_2993_, v_as_2994_, v_sz_boxed_3003_, v_i_boxed_3004_, v_b_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec_ref(v_as_2994_);
lean_dec_ref(v___x_2992_);
return v_res_3005_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2(void){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3008_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___x_3009_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0));
v___x_3010_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_3009_, v___x_3008_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object* v_declName_3013_, uint8_t v_isMeta_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v___x_3020_; lean_object* v_env_3024_; lean_object* v___y_3026_; lean_object* v___x_3039_; 
v___x_3020_ = lean_st_ref_get(v___y_3018_);
v_env_3024_ = lean_ctor_get(v___x_3020_, 0);
lean_inc_ref(v_env_3024_);
lean_dec(v___x_3020_);
v___x_3039_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3024_, v_declName_3013_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_dec_ref(v_env_3024_);
lean_dec(v_declName_3013_);
goto v___jp_3021_;
}
else
{
lean_object* v_val_3040_; lean_object* v___x_3041_; lean_object* v_modules_3042_; lean_object* v___x_3043_; uint8_t v___x_3044_; 
v_val_3040_ = lean_ctor_get(v___x_3039_, 0);
lean_inc(v_val_3040_);
lean_dec_ref_known(v___x_3039_, 1);
v___x_3041_ = l_Lean_Environment_header(v_env_3024_);
v_modules_3042_ = lean_ctor_get(v___x_3041_, 3);
lean_inc_ref(v_modules_3042_);
lean_dec_ref(v___x_3041_);
v___x_3043_ = lean_array_get_size(v_modules_3042_);
v___x_3044_ = lean_nat_dec_lt(v_val_3040_, v___x_3043_);
if (v___x_3044_ == 0)
{
lean_dec_ref(v_modules_3042_);
lean_dec(v_val_3040_);
lean_dec_ref(v_env_3024_);
lean_dec(v_declName_3013_);
goto v___jp_3021_;
}
else
{
lean_object* v___x_3045_; lean_object* v_env_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; uint8_t v___y_3050_; 
v___x_3045_ = lean_st_ref_get(v___y_3018_);
v_env_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc_ref(v_env_3046_);
lean_dec(v___x_3045_);
v___x_3047_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2);
v___x_3048_ = lean_array_fget(v_modules_3042_, v_val_3040_);
lean_dec(v_val_3040_);
lean_dec_ref(v_modules_3042_);
if (v_isMeta_3014_ == 0)
{
lean_dec_ref(v_env_3046_);
v___y_3050_ = v_isMeta_3014_;
goto v___jp_3049_;
}
else
{
uint8_t v___x_3061_; 
lean_inc(v_declName_3013_);
v___x_3061_ = l_Lean_isMarkedMeta(v_env_3046_, v_declName_3013_);
if (v___x_3061_ == 0)
{
v___y_3050_ = v_isMeta_3014_;
goto v___jp_3049_;
}
else
{
uint8_t v___x_3062_; 
v___x_3062_ = 0;
v___y_3050_ = v___x_3062_;
goto v___jp_3049_;
}
}
v___jp_3049_:
{
lean_object* v_toImport_3051_; lean_object* v_module_3052_; lean_object* v___x_3053_; 
v_toImport_3051_ = lean_ctor_get(v___x_3048_, 0);
lean_inc_ref(v_toImport_3051_);
lean_dec(v___x_3048_);
v_module_3052_ = lean_ctor_get(v_toImport_3051_, 0);
lean_inc(v_module_3052_);
lean_dec_ref(v_toImport_3051_);
lean_inc(v_declName_3013_);
v___x_3053_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_3052_, v___y_3050_, v_declName_3013_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
lean_dec_ref_known(v___x_3053_, 1);
v___x_3054_ = l_Lean_indirectModUseExt;
v___x_3055_ = lean_box(1);
v___x_3056_ = lean_box(0);
lean_inc_ref(v_env_3024_);
v___x_3057_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3047_, v___x_3054_, v_env_3024_, v___x_3055_, v___x_3056_);
v___x_3058_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3057_, v_declName_3013_);
lean_dec(v___x_3057_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v___x_3059_; 
v___x_3059_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3));
v___y_3026_ = v___x_3059_;
goto v___jp_3025_;
}
else
{
lean_object* v_val_3060_; 
v_val_3060_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_val_3060_);
lean_dec_ref_known(v___x_3058_, 1);
v___y_3026_ = v_val_3060_;
goto v___jp_3025_;
}
}
else
{
lean_dec_ref(v_env_3024_);
lean_dec(v_declName_3013_);
return v___x_3053_;
}
}
}
}
v___jp_3021_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = lean_box(0);
v___x_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3022_);
return v___x_3023_;
}
v___jp_3025_:
{
lean_object* v___x_3027_; size_t v_sz_3028_; size_t v___x_3029_; lean_object* v___x_3030_; 
v___x_3027_ = lean_box(0);
v_sz_3028_ = lean_array_size(v___y_3026_);
v___x_3029_ = ((size_t)0ULL);
v___x_3030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v_env_3024_, v_declName_3013_, v___y_3026_, v_sz_3028_, v___x_3029_, v___x_3027_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec_ref(v___y_3026_);
lean_dec_ref(v_env_3024_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3037_ == 0)
{
lean_object* v_unused_3038_; 
v_unused_3038_ = lean_ctor_get(v___x_3030_, 0);
lean_dec(v_unused_3038_);
v___x_3032_ = v___x_3030_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_dec(v___x_3030_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 0, v___x_3027_);
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3027_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
else
{
return v___x_3030_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object* v_declName_3063_, lean_object* v_isMeta_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
uint8_t v_isMeta_boxed_3070_; lean_object* v_res_3071_; 
v_isMeta_boxed_3070_ = lean_unbox(v_isMeta_3064_);
v_res_3071_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3063_, v_isMeta_boxed_3070_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
return v_res_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(lean_object* v___y_3072_, uint8_t v_isExporting_3073_, lean_object* v___x_3074_, lean_object* v___y_3075_, lean_object* v___x_3076_, lean_object* v_a_x3f_3077_){
_start:
{
lean_object* v___x_3079_; lean_object* v_env_3080_; lean_object* v_nextMacroScope_3081_; lean_object* v_ngen_3082_; lean_object* v_auxDeclNGen_3083_; lean_object* v_traceState_3084_; lean_object* v_messages_3085_; lean_object* v_infoState_3086_; lean_object* v_snapshotTasks_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3112_; 
v___x_3079_ = lean_st_ref_take(v___y_3072_);
v_env_3080_ = lean_ctor_get(v___x_3079_, 0);
v_nextMacroScope_3081_ = lean_ctor_get(v___x_3079_, 1);
v_ngen_3082_ = lean_ctor_get(v___x_3079_, 2);
v_auxDeclNGen_3083_ = lean_ctor_get(v___x_3079_, 3);
v_traceState_3084_ = lean_ctor_get(v___x_3079_, 4);
v_messages_3085_ = lean_ctor_get(v___x_3079_, 6);
v_infoState_3086_ = lean_ctor_get(v___x_3079_, 7);
v_snapshotTasks_3087_ = lean_ctor_get(v___x_3079_, 8);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3112_ == 0)
{
lean_object* v_unused_3113_; 
v_unused_3113_ = lean_ctor_get(v___x_3079_, 5);
lean_dec(v_unused_3113_);
v___x_3089_ = v___x_3079_;
v_isShared_3090_ = v_isSharedCheck_3112_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_snapshotTasks_3087_);
lean_inc(v_infoState_3086_);
lean_inc(v_messages_3085_);
lean_inc(v_traceState_3084_);
lean_inc(v_auxDeclNGen_3083_);
lean_inc(v_ngen_3082_);
lean_inc(v_nextMacroScope_3081_);
lean_inc(v_env_3080_);
lean_dec(v___x_3079_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3112_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3091_; lean_object* v___x_3093_; 
v___x_3091_ = l_Lean_Environment_setExporting(v_env_3080_, v_isExporting_3073_);
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 5, v___x_3074_);
lean_ctor_set(v___x_3089_, 0, v___x_3091_);
v___x_3093_ = v___x_3089_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3091_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v_nextMacroScope_3081_);
lean_ctor_set(v_reuseFailAlloc_3111_, 2, v_ngen_3082_);
lean_ctor_set(v_reuseFailAlloc_3111_, 3, v_auxDeclNGen_3083_);
lean_ctor_set(v_reuseFailAlloc_3111_, 4, v_traceState_3084_);
lean_ctor_set(v_reuseFailAlloc_3111_, 5, v___x_3074_);
lean_ctor_set(v_reuseFailAlloc_3111_, 6, v_messages_3085_);
lean_ctor_set(v_reuseFailAlloc_3111_, 7, v_infoState_3086_);
lean_ctor_set(v_reuseFailAlloc_3111_, 8, v_snapshotTasks_3087_);
v___x_3093_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v_mctx_3096_; lean_object* v_zetaDeltaFVarIds_3097_; lean_object* v_postponed_3098_; lean_object* v_diag_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3109_; 
v___x_3094_ = lean_st_ref_set(v___y_3072_, v___x_3093_);
v___x_3095_ = lean_st_ref_take(v___y_3075_);
v_mctx_3096_ = lean_ctor_get(v___x_3095_, 0);
v_zetaDeltaFVarIds_3097_ = lean_ctor_get(v___x_3095_, 2);
v_postponed_3098_ = lean_ctor_get(v___x_3095_, 3);
v_diag_3099_ = lean_ctor_get(v___x_3095_, 4);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3109_ == 0)
{
lean_object* v_unused_3110_; 
v_unused_3110_ = lean_ctor_get(v___x_3095_, 1);
lean_dec(v_unused_3110_);
v___x_3101_ = v___x_3095_;
v_isShared_3102_ = v_isSharedCheck_3109_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_diag_3099_);
lean_inc(v_postponed_3098_);
lean_inc(v_zetaDeltaFVarIds_3097_);
lean_inc(v_mctx_3096_);
lean_dec(v___x_3095_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3109_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 1, v___x_3076_);
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_mctx_3096_);
lean_ctor_set(v_reuseFailAlloc_3108_, 1, v___x_3076_);
lean_ctor_set(v_reuseFailAlloc_3108_, 2, v_zetaDeltaFVarIds_3097_);
lean_ctor_set(v_reuseFailAlloc_3108_, 3, v_postponed_3098_);
lean_ctor_set(v_reuseFailAlloc_3108_, 4, v_diag_3099_);
v___x_3104_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3105_ = lean_st_ref_set(v___y_3075_, v___x_3104_);
v___x_3106_ = lean_box(0);
v___x_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3106_);
return v___x_3107_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0___boxed(lean_object* v___y_3114_, lean_object* v_isExporting_3115_, lean_object* v___x_3116_, lean_object* v___y_3117_, lean_object* v___x_3118_, lean_object* v_a_x3f_3119_, lean_object* v___y_3120_){
_start:
{
uint8_t v_isExporting_boxed_3121_; lean_object* v_res_3122_; 
v_isExporting_boxed_3121_ = lean_unbox(v_isExporting_3115_);
v_res_3122_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3114_, v_isExporting_boxed_3121_, v___x_3116_, v___y_3117_, v___x_3118_, v_a_x3f_3119_);
lean_dec(v_a_x3f_3119_);
lean_dec(v___y_3117_);
lean_dec(v___y_3114_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(lean_object* v_x_3123_, uint8_t v_isExporting_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v___x_3130_; lean_object* v_env_3131_; uint8_t v_isExporting_3132_; lean_object* v___x_3198_; uint8_t v_isModule_3199_; 
v___x_3130_ = lean_st_ref_get(v___y_3128_);
v_env_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc_ref(v_env_3131_);
lean_dec(v___x_3130_);
v_isExporting_3132_ = lean_ctor_get_uint8(v_env_3131_, sizeof(void*)*8);
v___x_3198_ = l_Lean_Environment_header(v_env_3131_);
lean_dec_ref(v_env_3131_);
v_isModule_3199_ = lean_ctor_get_uint8(v___x_3198_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3198_);
if (v_isModule_3199_ == 0)
{
lean_object* v___x_3200_; 
lean_inc(v___y_3128_);
lean_inc_ref(v___y_3127_);
lean_inc(v___y_3126_);
lean_inc_ref(v___y_3125_);
v___x_3200_ = lean_apply_5(v_x_3123_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, lean_box(0));
return v___x_3200_;
}
else
{
if (v_isExporting_3132_ == 0)
{
if (v_isExporting_3124_ == 0)
{
lean_object* v___x_3201_; 
lean_inc(v___y_3128_);
lean_inc_ref(v___y_3127_);
lean_inc(v___y_3126_);
lean_inc_ref(v___y_3125_);
v___x_3201_ = lean_apply_5(v_x_3123_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, lean_box(0));
return v___x_3201_;
}
else
{
goto v___jp_3133_;
}
}
else
{
if (v_isExporting_3124_ == 0)
{
goto v___jp_3133_;
}
else
{
lean_object* v___x_3202_; 
lean_inc(v___y_3128_);
lean_inc_ref(v___y_3127_);
lean_inc(v___y_3126_);
lean_inc_ref(v___y_3125_);
v___x_3202_ = lean_apply_5(v_x_3123_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, lean_box(0));
return v___x_3202_;
}
}
}
v___jp_3133_:
{
lean_object* v___x_3134_; lean_object* v_env_3135_; lean_object* v_nextMacroScope_3136_; lean_object* v_ngen_3137_; lean_object* v_auxDeclNGen_3138_; lean_object* v_traceState_3139_; lean_object* v_messages_3140_; lean_object* v_infoState_3141_; lean_object* v_snapshotTasks_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3196_; 
v___x_3134_ = lean_st_ref_take(v___y_3128_);
v_env_3135_ = lean_ctor_get(v___x_3134_, 0);
v_nextMacroScope_3136_ = lean_ctor_get(v___x_3134_, 1);
v_ngen_3137_ = lean_ctor_get(v___x_3134_, 2);
v_auxDeclNGen_3138_ = lean_ctor_get(v___x_3134_, 3);
v_traceState_3139_ = lean_ctor_get(v___x_3134_, 4);
v_messages_3140_ = lean_ctor_get(v___x_3134_, 6);
v_infoState_3141_ = lean_ctor_get(v___x_3134_, 7);
v_snapshotTasks_3142_ = lean_ctor_get(v___x_3134_, 8);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3196_ == 0)
{
lean_object* v_unused_3197_; 
v_unused_3197_ = lean_ctor_get(v___x_3134_, 5);
lean_dec(v_unused_3197_);
v___x_3144_ = v___x_3134_;
v_isShared_3145_ = v_isSharedCheck_3196_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_snapshotTasks_3142_);
lean_inc(v_infoState_3141_);
lean_inc(v_messages_3140_);
lean_inc(v_traceState_3139_);
lean_inc(v_auxDeclNGen_3138_);
lean_inc(v_ngen_3137_);
lean_inc(v_nextMacroScope_3136_);
lean_inc(v_env_3135_);
lean_dec(v___x_3134_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3196_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3149_; 
v___x_3146_ = l_Lean_Environment_setExporting(v_env_3135_, v_isExporting_3124_);
v___x_3147_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 5, v___x_3147_);
lean_ctor_set(v___x_3144_, 0, v___x_3146_);
v___x_3149_ = v___x_3144_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3146_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v_nextMacroScope_3136_);
lean_ctor_set(v_reuseFailAlloc_3195_, 2, v_ngen_3137_);
lean_ctor_set(v_reuseFailAlloc_3195_, 3, v_auxDeclNGen_3138_);
lean_ctor_set(v_reuseFailAlloc_3195_, 4, v_traceState_3139_);
lean_ctor_set(v_reuseFailAlloc_3195_, 5, v___x_3147_);
lean_ctor_set(v_reuseFailAlloc_3195_, 6, v_messages_3140_);
lean_ctor_set(v_reuseFailAlloc_3195_, 7, v_infoState_3141_);
lean_ctor_set(v_reuseFailAlloc_3195_, 8, v_snapshotTasks_3142_);
v___x_3149_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v_mctx_3152_; lean_object* v_zetaDeltaFVarIds_3153_; lean_object* v_postponed_3154_; lean_object* v_diag_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3193_; 
v___x_3150_ = lean_st_ref_set(v___y_3128_, v___x_3149_);
v___x_3151_ = lean_st_ref_take(v___y_3126_);
v_mctx_3152_ = lean_ctor_get(v___x_3151_, 0);
v_zetaDeltaFVarIds_3153_ = lean_ctor_get(v___x_3151_, 2);
v_postponed_3154_ = lean_ctor_get(v___x_3151_, 3);
v_diag_3155_ = lean_ctor_get(v___x_3151_, 4);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3193_ == 0)
{
lean_object* v_unused_3194_; 
v_unused_3194_ = lean_ctor_get(v___x_3151_, 1);
lean_dec(v_unused_3194_);
v___x_3157_ = v___x_3151_;
v_isShared_3158_ = v_isSharedCheck_3193_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_diag_3155_);
lean_inc(v_postponed_3154_);
lean_inc(v_zetaDeltaFVarIds_3153_);
lean_inc(v_mctx_3152_);
lean_dec(v___x_3151_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3193_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3159_; lean_object* v___x_3161_; 
v___x_3159_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_3158_ == 0)
{
lean_ctor_set(v___x_3157_, 1, v___x_3159_);
v___x_3161_ = v___x_3157_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_mctx_3152_);
lean_ctor_set(v_reuseFailAlloc_3192_, 1, v___x_3159_);
lean_ctor_set(v_reuseFailAlloc_3192_, 2, v_zetaDeltaFVarIds_3153_);
lean_ctor_set(v_reuseFailAlloc_3192_, 3, v_postponed_3154_);
lean_ctor_set(v_reuseFailAlloc_3192_, 4, v_diag_3155_);
v___x_3161_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
lean_object* v___x_3162_; lean_object* v_r_3163_; 
v___x_3162_ = lean_st_ref_set(v___y_3126_, v___x_3161_);
lean_inc(v___y_3128_);
lean_inc_ref(v___y_3127_);
lean_inc(v___y_3126_);
lean_inc_ref(v___y_3125_);
v_r_3163_ = lean_apply_5(v_x_3123_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, lean_box(0));
if (lean_obj_tag(v_r_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3180_; 
v_a_3164_ = lean_ctor_get(v_r_3163_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v_r_3163_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3166_ = v_r_3163_;
v_isShared_3167_ = v_isSharedCheck_3180_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v_r_3163_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3180_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
lean_inc(v_a_3164_);
if (v_isShared_3167_ == 0)
{
lean_ctor_set_tag(v___x_3166_, 1);
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
lean_object* v___x_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
v___x_3170_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3128_, v_isExporting_3132_, v___x_3147_, v___y_3126_, v___x_3159_, v___x_3169_);
lean_dec_ref(v___x_3169_);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3177_ == 0)
{
lean_object* v_unused_3178_; 
v_unused_3178_ = lean_ctor_get(v___x_3170_, 0);
lean_dec(v_unused_3178_);
v___x_3172_ = v___x_3170_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_dec(v___x_3170_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 0, v_a_3164_);
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3164_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
v_a_3181_ = lean_ctor_get(v_r_3163_, 0);
lean_inc(v_a_3181_);
lean_dec_ref_known(v_r_3163_, 1);
v___x_3182_ = lean_box(0);
v___x_3183_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3128_, v_isExporting_3132_, v___x_3147_, v___y_3126_, v___x_3159_, v___x_3182_);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3190_ == 0)
{
lean_object* v_unused_3191_; 
v_unused_3191_ = lean_ctor_get(v___x_3183_, 0);
lean_dec(v_unused_3191_);
v___x_3185_ = v___x_3183_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_dec(v___x_3183_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
lean_ctor_set_tag(v___x_3185_, 1);
lean_ctor_set(v___x_3185_, 0, v_a_3181_);
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3181_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___boxed(lean_object* v_x_3203_, lean_object* v_isExporting_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
uint8_t v_isExporting_boxed_3210_; lean_object* v_res_3211_; 
v_isExporting_boxed_3210_ = lean_unbox(v_isExporting_3204_);
v_res_3211_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3203_, v_isExporting_boxed_3210_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object* v_x_3212_, uint8_t v_when_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
if (v_when_3213_ == 0)
{
lean_object* v___x_3219_; 
lean_inc(v___y_3217_);
lean_inc_ref(v___y_3216_);
lean_inc(v___y_3215_);
lean_inc_ref(v___y_3214_);
v___x_3219_ = lean_apply_5(v_x_3212_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, lean_box(0));
return v___x_3219_;
}
else
{
uint8_t v___x_3220_; lean_object* v___x_3221_; 
v___x_3220_ = 0;
v___x_3221_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3212_, v___x_3220_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
return v___x_3221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object* v_x_3222_, lean_object* v_when_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
uint8_t v_when_boxed_3229_; lean_object* v_res_3230_; 
v_when_boxed_3229_ = lean_unbox(v_when_3223_);
v_res_3230_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3222_, v_when_boxed_3229_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object* v___x_3231_, lean_object* v_ext_3232_, uint8_t v_showInfo_3233_, uint8_t v_minIndexable_3234_, lean_object* v_attrName_3235_, lean_object* v_declName_3236_, lean_object* v_stx_3237_, uint8_t v_attrKind_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
uint8_t v___x_3242_; uint8_t v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___y_3259_; lean_object* v___x_3269_; 
v___x_3242_ = 0;
v___x_3243_ = 1;
v___x_3244_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_3245_ = lean_unsigned_to_nat(32u);
v___x_3246_ = lean_mk_empty_array_with_capacity(v___x_3245_);
lean_dec_ref(v___x_3246_);
v___x_3247_ = lean_unsigned_to_nat(0u);
v___x_3248_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_3249_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5);
v___x_3250_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6));
v___x_3251_ = lean_box(0);
lean_inc(v___x_3231_);
v___x_3252_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3252_, 0, v___x_3244_);
lean_ctor_set(v___x_3252_, 1, v___x_3231_);
lean_ctor_set(v___x_3252_, 2, v___x_3249_);
lean_ctor_set(v___x_3252_, 3, v___x_3250_);
lean_ctor_set(v___x_3252_, 4, v___x_3251_);
lean_ctor_set(v___x_3252_, 5, v___x_3247_);
lean_ctor_set(v___x_3252_, 6, v___x_3251_);
lean_ctor_set_uint8(v___x_3252_, sizeof(void*)*7, v___x_3242_);
lean_ctor_set_uint8(v___x_3252_, sizeof(void*)*7 + 1, v___x_3242_);
lean_ctor_set_uint8(v___x_3252_, sizeof(void*)*7 + 2, v___x_3242_);
lean_ctor_set_uint8(v___x_3252_, sizeof(void*)*7 + 3, v___x_3243_);
v___x_3253_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_3254_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_3255_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9);
v___x_3256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3253_);
lean_ctor_set(v___x_3256_, 1, v___x_3254_);
lean_ctor_set(v___x_3256_, 2, v___x_3231_);
lean_ctor_set(v___x_3256_, 3, v___x_3248_);
lean_ctor_set(v___x_3256_, 4, v___x_3255_);
v___x_3257_ = lean_st_mk_ref(v___x_3256_);
lean_inc(v_declName_3236_);
v___x_3269_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3236_, v___x_3242_, v___x_3252_, v___x_3257_, v___y_3239_, v___y_3240_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___f_3274_; lean_object* v___x_3275_; 
lean_dec_ref_known(v___x_3269_, 1);
v___x_3270_ = lean_box(v_attrKind_3238_);
v___x_3271_ = lean_box(v_showInfo_3233_);
v___x_3272_ = lean_box(v_minIndexable_3234_);
v___x_3273_ = lean_box(v___x_3242_);
v___f_3274_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed), 13, 8);
lean_closure_set(v___f_3274_, 0, v_stx_3237_);
lean_closure_set(v___f_3274_, 1, v_ext_3232_);
lean_closure_set(v___f_3274_, 2, v_declName_3236_);
lean_closure_set(v___f_3274_, 3, v___x_3270_);
lean_closure_set(v___f_3274_, 4, v___x_3271_);
lean_closure_set(v___f_3274_, 5, v___x_3272_);
lean_closure_set(v___f_3274_, 6, v___x_3273_);
lean_closure_set(v___f_3274_, 7, v_attrName_3235_);
v___x_3275_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v___f_3274_, v___x_3243_, v___x_3252_, v___x_3257_, v___y_3239_, v___y_3240_);
lean_dec_ref_known(v___x_3252_, 7);
v___y_3259_ = v___x_3275_;
goto v___jp_3258_;
}
else
{
lean_dec_ref_known(v___x_3252_, 7);
lean_dec(v_stx_3237_);
lean_dec(v_declName_3236_);
lean_dec(v_attrName_3235_);
lean_dec_ref(v_ext_3232_);
v___y_3259_ = v___x_3269_;
goto v___jp_3258_;
}
v___jp_3258_:
{
if (lean_obj_tag(v___y_3259_) == 0)
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3268_; 
v_a_3260_ = lean_ctor_get(v___y_3259_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___y_3259_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3262_ = v___y_3259_;
v_isShared_3263_ = v_isSharedCheck_3268_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___y_3259_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3268_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3264_; lean_object* v___x_3266_; 
v___x_3264_ = lean_st_ref_get(v___x_3257_);
lean_dec(v___x_3257_);
lean_dec(v___x_3264_);
if (v_isShared_3263_ == 0)
{
v___x_3266_ = v___x_3262_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3260_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
else
{
lean_dec(v___x_3257_);
return v___y_3259_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object* v___x_3276_, lean_object* v_ext_3277_, lean_object* v_showInfo_3278_, lean_object* v_minIndexable_3279_, lean_object* v_attrName_3280_, lean_object* v_declName_3281_, lean_object* v_stx_3282_, lean_object* v_attrKind_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
uint8_t v_showInfo_boxed_3287_; uint8_t v_minIndexable_boxed_3288_; uint8_t v_attrKind_boxed_3289_; lean_object* v_res_3290_; 
v_showInfo_boxed_3287_ = lean_unbox(v_showInfo_3278_);
v_minIndexable_boxed_3288_ = lean_unbox(v_minIndexable_3279_);
v_attrKind_boxed_3289_ = lean_unbox(v_attrKind_3283_);
v_res_3290_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(v___x_3276_, v_ext_3277_, v_showInfo_boxed_3287_, v_minIndexable_boxed_3288_, v_attrName_3280_, v_declName_3281_, v_stx_3282_, v_attrKind_boxed_3289_, v___y_3284_, v___y_3285_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object* v_attrName_3313_, uint8_t v_minIndexable_3314_, uint8_t v_showInfo_3315_, lean_object* v_ext_3316_, lean_object* v_ref_3317_){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___f_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___f_3324_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3370_; 
v___x_3319_ = lean_box(1);
v___x_3320_ = lean_box(v_showInfo_3315_);
lean_inc_n(v_attrName_3313_, 2);
lean_inc_ref(v_ext_3316_);
v___f_3321_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed), 8, 4);
lean_closure_set(v___f_3321_, 0, v___x_3319_);
lean_closure_set(v___f_3321_, 1, v_ext_3316_);
lean_closure_set(v___f_3321_, 2, v___x_3320_);
lean_closure_set(v___f_3321_, 3, v_attrName_3313_);
v___x_3322_ = lean_box(v_showInfo_3315_);
v___x_3323_ = lean_box(v_minIndexable_3314_);
v___f_3324_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed), 11, 5);
lean_closure_set(v___f_3324_, 0, v___x_3319_);
lean_closure_set(v___f_3324_, 1, v_ext_3316_);
lean_closure_set(v___f_3324_, 2, v___x_3322_);
lean_closure_set(v___f_3324_, 3, v___x_3323_);
lean_closure_set(v___f_3324_, 4, v_attrName_3313_);
if (v_minIndexable_3314_ == 0)
{
if (v_showInfo_3315_ == 0)
{
lean_inc(v_attrName_3313_);
v___y_3370_ = v_attrName_3313_;
goto v___jp_3369_;
}
else
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19));
lean_inc(v_attrName_3313_);
v___x_3399_ = lean_name_append_after(v_attrName_3313_, v___x_3398_);
v___y_3370_ = v___x_3399_;
goto v___jp_3369_;
}
}
else
{
if (v_showInfo_3315_ == 0)
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20));
lean_inc(v_attrName_3313_);
v___x_3401_ = lean_name_append_after(v_attrName_3313_, v___x_3400_);
v___y_3370_ = v___x_3401_;
goto v___jp_3369_;
}
else
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
v___x_3402_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21));
lean_inc(v_attrName_3313_);
v___x_3403_ = lean_name_append_after(v_attrName_3313_, v___x_3402_);
v___y_3370_ = v___x_3403_;
goto v___jp_3369_;
}
}
v___jp_3325_:
{
lean_object* v___x_3328_; uint8_t v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; uint8_t v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0));
v___x_3329_ = 1;
v___x_3330_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3313_, v___x_3329_);
v___x_3331_ = lean_string_append(v___x_3328_, v___x_3330_);
v___x_3332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1));
v___x_3333_ = lean_string_append(v___x_3331_, v___x_3332_);
v___x_3334_ = lean_string_append(v___x_3333_, v___x_3330_);
v___x_3335_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2));
v___x_3336_ = lean_string_append(v___x_3334_, v___x_3335_);
v___x_3337_ = lean_string_append(v___x_3336_, v___x_3330_);
v___x_3338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3));
v___x_3339_ = lean_string_append(v___x_3337_, v___x_3338_);
v___x_3340_ = lean_string_append(v___x_3339_, v___x_3330_);
v___x_3341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4));
v___x_3342_ = lean_string_append(v___x_3340_, v___x_3341_);
v___x_3343_ = lean_string_append(v___x_3342_, v___x_3330_);
v___x_3344_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5));
v___x_3345_ = lean_string_append(v___x_3343_, v___x_3344_);
v___x_3346_ = lean_string_append(v___x_3345_, v___x_3330_);
v___x_3347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6));
v___x_3348_ = lean_string_append(v___x_3346_, v___x_3347_);
v___x_3349_ = lean_string_append(v___x_3348_, v___x_3330_);
v___x_3350_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7));
v___x_3351_ = lean_string_append(v___x_3349_, v___x_3350_);
v___x_3352_ = lean_string_append(v___x_3351_, v___x_3330_);
v___x_3353_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8));
v___x_3354_ = lean_string_append(v___x_3352_, v___x_3353_);
v___x_3355_ = lean_string_append(v___x_3354_, v___x_3330_);
v___x_3356_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9));
v___x_3357_ = lean_string_append(v___x_3355_, v___x_3356_);
v___x_3358_ = lean_string_append(v___x_3357_, v___x_3330_);
v___x_3359_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10));
v___x_3360_ = lean_string_append(v___x_3358_, v___x_3359_);
v___x_3361_ = lean_string_append(v___x_3360_, v___x_3330_);
lean_dec_ref(v___x_3330_);
v___x_3362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11));
v___x_3363_ = lean_string_append(v___x_3361_, v___x_3362_);
v___x_3364_ = lean_string_append(v___y_3327_, v___x_3363_);
lean_dec_ref(v___x_3363_);
v___x_3365_ = 1;
v___x_3366_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3366_, 0, v_ref_3317_);
lean_ctor_set(v___x_3366_, 1, v___y_3326_);
lean_ctor_set(v___x_3366_, 2, v___x_3364_);
lean_ctor_set_uint8(v___x_3366_, sizeof(void*)*3, v___x_3365_);
v___x_3367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3366_);
lean_ctor_set(v___x_3367_, 1, v___f_3324_);
lean_ctor_set(v___x_3367_, 2, v___f_3321_);
v___x_3368_ = l_Lean_registerBuiltinAttribute(v___x_3367_);
return v___x_3368_;
}
v___jp_3369_:
{
if (v_minIndexable_3314_ == 0)
{
if (v_showInfo_3315_ == 0)
{
lean_object* v___x_3371_; uint8_t v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3371_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
v___x_3372_ = 1;
lean_inc(v_attrName_3313_);
v___x_3373_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3313_, v___x_3372_);
v___x_3374_ = lean_string_append(v___x_3371_, v___x_3373_);
lean_dec_ref(v___x_3373_);
v___x_3375_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13));
v___x_3376_ = lean_string_append(v___x_3374_, v___x_3375_);
v___y_3326_ = v___y_3370_;
v___y_3327_ = v___x_3376_;
goto v___jp_3325_;
}
else
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3377_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3313_);
v___x_3378_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3313_, v_showInfo_3315_);
v___x_3379_ = lean_string_append(v___x_3377_, v___x_3378_);
v___x_3380_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14));
v___x_3381_ = lean_string_append(v___x_3379_, v___x_3380_);
v___x_3382_ = lean_string_append(v___x_3381_, v___x_3378_);
lean_dec_ref(v___x_3378_);
v___x_3383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15));
v___x_3384_ = lean_string_append(v___x_3382_, v___x_3383_);
v___y_3326_ = v___y_3370_;
v___y_3327_ = v___x_3384_;
goto v___jp_3325_;
}
}
else
{
if (v_showInfo_3315_ == 0)
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3385_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3313_);
v___x_3386_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3313_, v_minIndexable_3314_);
v___x_3387_ = lean_string_append(v___x_3385_, v___x_3386_);
lean_dec_ref(v___x_3386_);
v___x_3388_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16));
v___x_3389_ = lean_string_append(v___x_3387_, v___x_3388_);
v___y_3326_ = v___y_3370_;
v___y_3327_ = v___x_3389_;
goto v___jp_3325_;
}
else
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3390_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3313_);
v___x_3391_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3313_, v_showInfo_3315_);
v___x_3392_ = lean_string_append(v___x_3390_, v___x_3391_);
v___x_3393_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17));
v___x_3394_ = lean_string_append(v___x_3392_, v___x_3393_);
v___x_3395_ = lean_string_append(v___x_3394_, v___x_3391_);
lean_dec_ref(v___x_3391_);
v___x_3396_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18));
v___x_3397_ = lean_string_append(v___x_3395_, v___x_3396_);
v___y_3326_ = v___y_3370_;
v___y_3327_ = v___x_3397_;
goto v___jp_3325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object* v_attrName_3404_, lean_object* v_minIndexable_3405_, lean_object* v_showInfo_3406_, lean_object* v_ext_3407_, lean_object* v_ref_3408_, lean_object* v_a_3409_){
_start:
{
uint8_t v_minIndexable_boxed_3410_; uint8_t v_showInfo_boxed_3411_; lean_object* v_res_3412_; 
v_minIndexable_boxed_3410_ = lean_unbox(v_minIndexable_3405_);
v_showInfo_boxed_3411_ = lean_unbox(v_showInfo_3406_);
v_res_3412_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3404_, v_minIndexable_boxed_3410_, v_showInfo_boxed_3411_, v_ext_3407_, v_ref_3408_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object* v_00_u03b1_3413_, lean_object* v_msg_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
lean_object* v___x_3420_; 
v___x_3420_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
return v___x_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object* v_00_u03b1_3421_, lean_object* v_msg_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(v_00_u03b1_3421_, v_msg_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object* v_ext_3429_, uint8_t v_attrKind_3430_, uint8_t v_showInfo_3431_, uint8_t v_minIndexable_3432_, lean_object* v_as_3433_, lean_object* v_as_x27_3434_, lean_object* v_b_3435_, lean_object* v_a_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v___x_3442_; 
v___x_3442_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3429_, v_attrKind_3430_, v_showInfo_3431_, v_minIndexable_3432_, v_as_x27_3434_, v_b_3435_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object* v_ext_3443_, lean_object* v_attrKind_3444_, lean_object* v_showInfo_3445_, lean_object* v_minIndexable_3446_, lean_object* v_as_3447_, lean_object* v_as_x27_3448_, lean_object* v_b_3449_, lean_object* v_a_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
uint8_t v_attrKind_boxed_3456_; uint8_t v_showInfo_boxed_3457_; uint8_t v_minIndexable_boxed_3458_; lean_object* v_res_3459_; 
v_attrKind_boxed_3456_ = lean_unbox(v_attrKind_3444_);
v_showInfo_boxed_3457_ = lean_unbox(v_showInfo_3445_);
v_minIndexable_boxed_3458_ = lean_unbox(v_minIndexable_3446_);
v_res_3459_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(v_ext_3443_, v_attrKind_boxed_3456_, v_showInfo_boxed_3457_, v_minIndexable_boxed_3458_, v_as_3447_, v_as_x27_3448_, v_b_3449_, v_a_3450_, v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_);
lean_dec(v___y_3454_);
lean_dec_ref(v___y_3453_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v_as_x27_3448_);
lean_dec(v_as_3447_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(lean_object* v_00_u03b1_3460_, lean_object* v_x_3461_, uint8_t v_isExporting_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v___x_3468_; 
v___x_3468_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3461_, v_isExporting_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___boxed(lean_object* v_00_u03b1_3469_, lean_object* v_x_3470_, lean_object* v_isExporting_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
uint8_t v_isExporting_boxed_3477_; lean_object* v_res_3478_; 
v_isExporting_boxed_3477_ = lean_unbox(v_isExporting_3471_);
v_res_3478_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(v_00_u03b1_3469_, v_x_3470_, v_isExporting_boxed_3477_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object* v_00_u03b1_3479_, lean_object* v_x_3480_, uint8_t v_when_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
lean_object* v___x_3487_; 
v___x_3487_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3480_, v_when_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object* v_00_u03b1_3488_, lean_object* v_x_3489_, lean_object* v_when_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
uint8_t v_when_boxed_3496_; lean_object* v_res_3497_; 
v_when_boxed_3496_ = lean_unbox(v_when_3490_);
v_res_3497_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(v_00_u03b1_3488_, v_x_3489_, v_when_boxed_3496_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(lean_object* v_00_u03b2_3498_, lean_object* v_m_3499_, lean_object* v_a_3500_){
_start:
{
lean_object* v___x_3501_; 
v___x_3501_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_3499_, v_a_3500_);
return v___x_3501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3502_, lean_object* v_m_3503_, lean_object* v_a_3504_){
_start:
{
lean_object* v_res_3505_; 
v_res_3505_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(v_00_u03b2_3502_, v_m_3503_, v_a_3504_);
lean_dec(v_a_3504_);
lean_dec_ref(v_m_3503_);
return v_res_3505_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3506_, lean_object* v_x_3507_, lean_object* v_x_3508_){
_start:
{
uint8_t v___x_3509_; 
v___x_3509_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_3507_, v_x_3508_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3510_, lean_object* v_x_3511_, lean_object* v_x_3512_){
_start:
{
uint8_t v_res_3513_; lean_object* v_r_3514_; 
v_res_3513_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(v_00_u03b2_3510_, v_x_3511_, v_x_3512_);
lean_dec_ref(v_x_3512_);
lean_dec_ref(v_x_3511_);
v_r_3514_ = lean_box(v_res_3513_);
return v_r_3514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_3515_, lean_object* v_a_3516_, lean_object* v_x_3517_){
_start:
{
lean_object* v___x_3518_; 
v___x_3518_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_3516_, v_x_3517_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3519_, lean_object* v_a_3520_, lean_object* v_x_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(v_00_u03b2_3519_, v_a_3520_, v_x_3521_);
lean_dec(v_x_3521_);
lean_dec(v_a_3520_);
return v_res_3522_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_3523_, lean_object* v_x_3524_, size_t v_x_3525_, lean_object* v_x_3526_){
_start:
{
uint8_t v___x_3527_; 
v___x_3527_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_3524_, v_x_3525_, v_x_3526_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3528_, lean_object* v_x_3529_, lean_object* v_x_3530_, lean_object* v_x_3531_){
_start:
{
size_t v_x_17383__boxed_3532_; uint8_t v_res_3533_; lean_object* v_r_3534_; 
v_x_17383__boxed_3532_ = lean_unbox_usize(v_x_3530_);
lean_dec(v_x_3530_);
v_res_3533_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(v_00_u03b2_3528_, v_x_3529_, v_x_17383__boxed_3532_, v_x_3531_);
lean_dec_ref(v_x_3531_);
lean_dec_ref(v_x_3529_);
v_r_3534_ = lean_box(v_res_3533_);
return v_r_3534_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_3535_, lean_object* v_keys_3536_, lean_object* v_vals_3537_, lean_object* v_heq_3538_, lean_object* v_i_3539_, lean_object* v_k_3540_){
_start:
{
uint8_t v___x_3541_; 
v___x_3541_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_3536_, v_i_3539_, v_k_3540_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_3542_, lean_object* v_keys_3543_, lean_object* v_vals_3544_, lean_object* v_heq_3545_, lean_object* v_i_3546_, lean_object* v_k_3547_){
_start:
{
uint8_t v_res_3548_; lean_object* v_r_3549_; 
v_res_3548_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(v_00_u03b2_3542_, v_keys_3543_, v_vals_3544_, v_heq_3545_, v_i_3546_, v_k_3547_);
lean_dec_ref(v_k_3547_);
lean_dec_ref(v_vals_3544_);
lean_dec_ref(v_keys_3543_);
v_r_3549_ = lean_box(v_res_3548_);
return v_r_3549_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3550_ = lean_box(0);
v___x_3551_ = lean_unsigned_to_nat(16u);
v___x_3552_ = lean_mk_array(v___x_3551_, v___x_3550_);
return v___x_3552_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3553_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3554_ = lean_unsigned_to_nat(0u);
v___x_3555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3554_);
lean_ctor_set(v___x_3555_, 1, v___x_3553_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3557_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3558_ = lean_st_mk_ref(v___x_3557_);
v___x_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3558_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object* v_a_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object* v_cls_3562_, lean_object* v_msg_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_){
_start:
{
lean_object* v_ref_3567_; lean_object* v___x_3568_; lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3613_; 
v_ref_3567_ = lean_ctor_get(v___y_3564_, 5);
v___x_3568_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_3563_, v___y_3564_, v___y_3565_);
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3571_ = v___x_3568_;
v_isShared_3572_ = v_isSharedCheck_3613_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3568_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3613_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3573_; lean_object* v_traceState_3574_; lean_object* v_env_3575_; lean_object* v_nextMacroScope_3576_; lean_object* v_ngen_3577_; lean_object* v_auxDeclNGen_3578_; lean_object* v_cache_3579_; lean_object* v_messages_3580_; lean_object* v_infoState_3581_; lean_object* v_snapshotTasks_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3612_; 
v___x_3573_ = lean_st_ref_take(v___y_3565_);
v_traceState_3574_ = lean_ctor_get(v___x_3573_, 4);
v_env_3575_ = lean_ctor_get(v___x_3573_, 0);
v_nextMacroScope_3576_ = lean_ctor_get(v___x_3573_, 1);
v_ngen_3577_ = lean_ctor_get(v___x_3573_, 2);
v_auxDeclNGen_3578_ = lean_ctor_get(v___x_3573_, 3);
v_cache_3579_ = lean_ctor_get(v___x_3573_, 5);
v_messages_3580_ = lean_ctor_get(v___x_3573_, 6);
v_infoState_3581_ = lean_ctor_get(v___x_3573_, 7);
v_snapshotTasks_3582_ = lean_ctor_get(v___x_3573_, 8);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3584_ = v___x_3573_;
v_isShared_3585_ = v_isSharedCheck_3612_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_snapshotTasks_3582_);
lean_inc(v_infoState_3581_);
lean_inc(v_messages_3580_);
lean_inc(v_cache_3579_);
lean_inc(v_traceState_3574_);
lean_inc(v_auxDeclNGen_3578_);
lean_inc(v_ngen_3577_);
lean_inc(v_nextMacroScope_3576_);
lean_inc(v_env_3575_);
lean_dec(v___x_3573_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3612_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
uint64_t v_tid_3586_; lean_object* v_traces_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3611_; 
v_tid_3586_ = lean_ctor_get_uint64(v_traceState_3574_, sizeof(void*)*1);
v_traces_3587_ = lean_ctor_get(v_traceState_3574_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v_traceState_3574_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3589_ = v_traceState_3574_;
v_isShared_3590_ = v_isSharedCheck_3611_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_traces_3587_);
lean_dec(v_traceState_3574_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3611_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3591_; double v___x_3592_; uint8_t v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3601_; 
v___x_3591_ = lean_box(0);
v___x_3592_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_3593_ = 0;
v___x_3594_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_3595_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3595_, 0, v_cls_3562_);
lean_ctor_set(v___x_3595_, 1, v___x_3591_);
lean_ctor_set(v___x_3595_, 2, v___x_3594_);
lean_ctor_set_float(v___x_3595_, sizeof(void*)*3, v___x_3592_);
lean_ctor_set_float(v___x_3595_, sizeof(void*)*3 + 8, v___x_3592_);
lean_ctor_set_uint8(v___x_3595_, sizeof(void*)*3 + 16, v___x_3593_);
v___x_3596_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_3597_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3595_);
lean_ctor_set(v___x_3597_, 1, v_a_3569_);
lean_ctor_set(v___x_3597_, 2, v___x_3596_);
lean_inc(v_ref_3567_);
v___x_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3598_, 0, v_ref_3567_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
v___x_3599_ = l_Lean_PersistentArray_push___redArg(v_traces_3587_, v___x_3598_);
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 0, v___x_3599_);
v___x_3601_ = v___x_3589_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3599_);
lean_ctor_set_uint64(v_reuseFailAlloc_3610_, sizeof(void*)*1, v_tid_3586_);
v___x_3601_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
lean_object* v___x_3603_; 
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 4, v___x_3601_);
v___x_3603_ = v___x_3584_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_env_3575_);
lean_ctor_set(v_reuseFailAlloc_3609_, 1, v_nextMacroScope_3576_);
lean_ctor_set(v_reuseFailAlloc_3609_, 2, v_ngen_3577_);
lean_ctor_set(v_reuseFailAlloc_3609_, 3, v_auxDeclNGen_3578_);
lean_ctor_set(v_reuseFailAlloc_3609_, 4, v___x_3601_);
lean_ctor_set(v_reuseFailAlloc_3609_, 5, v_cache_3579_);
lean_ctor_set(v_reuseFailAlloc_3609_, 6, v_messages_3580_);
lean_ctor_set(v_reuseFailAlloc_3609_, 7, v_infoState_3581_);
lean_ctor_set(v_reuseFailAlloc_3609_, 8, v_snapshotTasks_3582_);
v___x_3603_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3607_; 
v___x_3604_ = lean_st_ref_set(v___y_3565_, v___x_3603_);
v___x_3605_ = lean_box(0);
if (v_isShared_3572_ == 0)
{
lean_ctor_set(v___x_3571_, 0, v___x_3605_);
v___x_3607_ = v___x_3571_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v___x_3605_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_cls_3614_, lean_object* v_msg_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3614_, v_msg_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object* v_mod_3620_, uint8_t v_isMeta_3621_, lean_object* v_hint_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v___x_3626_; lean_object* v_env_3627_; uint8_t v_isExporting_3628_; lean_object* v___x_3629_; lean_object* v_env_3630_; lean_object* v___x_3631_; lean_object* v_entry_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___y_3637_; lean_object* v___x_3662_; uint8_t v___x_3663_; 
v___x_3626_ = lean_st_ref_get(v___y_3624_);
v_env_3627_ = lean_ctor_get(v___x_3626_, 0);
lean_inc_ref(v_env_3627_);
lean_dec(v___x_3626_);
v_isExporting_3628_ = lean_ctor_get_uint8(v_env_3627_, sizeof(void*)*8);
lean_dec_ref(v_env_3627_);
v___x_3629_ = lean_st_ref_get(v___y_3624_);
v_env_3630_ = lean_ctor_get(v___x_3629_, 0);
lean_inc_ref(v_env_3630_);
lean_dec(v___x_3629_);
v___x_3631_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2);
lean_inc(v_mod_3620_);
v_entry_3632_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3632_, 0, v_mod_3620_);
lean_ctor_set_uint8(v_entry_3632_, sizeof(void*)*1, v_isExporting_3628_);
lean_ctor_set_uint8(v_entry_3632_, sizeof(void*)*1 + 1, v_isMeta_3621_);
v___x_3633_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3634_ = lean_box(1);
v___x_3635_ = lean_box(0);
v___x_3662_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3631_, v___x_3633_, v_env_3630_, v___x_3634_, v___x_3635_);
v___x_3663_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_3662_, v_entry_3632_);
lean_dec(v___x_3662_);
if (v___x_3663_ == 0)
{
lean_object* v_options_3664_; uint8_t v_hasTrace_3665_; 
v_options_3664_ = lean_ctor_get(v___y_3623_, 2);
v_hasTrace_3665_ = lean_ctor_get_uint8(v_options_3664_, sizeof(void*)*1);
if (v_hasTrace_3665_ == 0)
{
lean_dec(v_hint_3622_);
lean_dec(v_mod_3620_);
v___y_3637_ = v___y_3624_;
goto v___jp_3636_;
}
else
{
lean_object* v_inheritedTraceOptions_3666_; lean_object* v_cls_3667_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v___x_3687_; uint8_t v___x_3688_; 
v_inheritedTraceOptions_3666_ = lean_ctor_get(v___y_3623_, 13);
v_cls_3667_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_3687_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
v___x_3688_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3666_, v_options_3664_, v___x_3687_);
if (v___x_3688_ == 0)
{
lean_dec(v_hint_3622_);
lean_dec(v_mod_3620_);
v___y_3637_ = v___y_3624_;
goto v___jp_3636_;
}
else
{
lean_object* v___x_3689_; lean_object* v___y_3691_; 
v___x_3689_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
if (v_isExporting_3628_ == 0)
{
lean_object* v___x_3698_; 
v___x_3698_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19));
v___y_3691_ = v___x_3698_;
goto v___jp_3690_;
}
else
{
lean_object* v___x_3699_; 
v___x_3699_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20));
v___y_3691_ = v___x_3699_;
goto v___jp_3690_;
}
v___jp_3690_:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
lean_inc_ref(v___y_3691_);
v___x_3692_ = l_Lean_stringToMessageData(v___y_3691_);
v___x_3693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3689_);
lean_ctor_set(v___x_3693_, 1, v___x_3692_);
v___x_3694_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16);
v___x_3695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3693_);
lean_ctor_set(v___x_3695_, 1, v___x_3694_);
if (v_isMeta_3621_ == 0)
{
lean_object* v___x_3696_; 
v___x_3696_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_3674_ = v___x_3695_;
v___y_3675_ = v___x_3696_;
goto v___jp_3673_;
}
else
{
lean_object* v___x_3697_; 
v___x_3697_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_3674_ = v___x_3695_;
v___y_3675_ = v___x_3697_;
goto v___jp_3673_;
}
}
}
v___jp_3668_:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3671_, 0, v___y_3669_);
lean_ctor_set(v___x_3671_, 1, v___y_3670_);
v___x_3672_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3667_, v___x_3671_, v___y_3623_, v___y_3624_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_dec_ref_known(v___x_3672_, 1);
v___y_3637_ = v___y_3624_;
goto v___jp_3636_;
}
else
{
lean_dec_ref_known(v_entry_3632_, 1);
return v___x_3672_;
}
}
v___jp_3673_:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; uint8_t v___x_3682_; 
lean_inc_ref(v___y_3675_);
v___x_3676_ = l_Lean_stringToMessageData(v___y_3675_);
v___x_3677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3677_, 0, v___y_3674_);
lean_ctor_set(v___x_3677_, 1, v___x_3676_);
v___x_3678_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_3679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3677_);
lean_ctor_set(v___x_3679_, 1, v___x_3678_);
v___x_3680_ = l_Lean_MessageData_ofName(v_mod_3620_);
v___x_3681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3679_);
lean_ctor_set(v___x_3681_, 1, v___x_3680_);
v___x_3682_ = l_Lean_Name_isAnonymous(v_hint_3622_);
if (v___x_3682_ == 0)
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3683_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8);
v___x_3684_ = l_Lean_MessageData_ofName(v_hint_3622_);
v___x_3685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3683_);
lean_ctor_set(v___x_3685_, 1, v___x_3684_);
v___y_3669_ = v___x_3681_;
v___y_3670_ = v___x_3685_;
goto v___jp_3668_;
}
else
{
lean_object* v___x_3686_; 
lean_dec(v_hint_3622_);
v___x_3686_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9);
v___y_3669_ = v___x_3681_;
v___y_3670_ = v___x_3686_;
goto v___jp_3668_;
}
}
}
}
else
{
lean_object* v___x_3700_; lean_object* v___x_3701_; 
lean_dec_ref_known(v_entry_3632_, 1);
lean_dec(v_hint_3622_);
lean_dec(v_mod_3620_);
v___x_3700_ = lean_box(0);
v___x_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3700_);
return v___x_3701_;
}
v___jp_3636_:
{
lean_object* v___x_3638_; lean_object* v_toEnvExtension_3639_; lean_object* v_env_3640_; lean_object* v_nextMacroScope_3641_; lean_object* v_ngen_3642_; lean_object* v_auxDeclNGen_3643_; lean_object* v_traceState_3644_; lean_object* v_messages_3645_; lean_object* v_infoState_3646_; lean_object* v_snapshotTasks_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3660_; 
v___x_3638_ = lean_st_ref_take(v___y_3637_);
v_toEnvExtension_3639_ = lean_ctor_get(v___x_3633_, 0);
v_env_3640_ = lean_ctor_get(v___x_3638_, 0);
v_nextMacroScope_3641_ = lean_ctor_get(v___x_3638_, 1);
v_ngen_3642_ = lean_ctor_get(v___x_3638_, 2);
v_auxDeclNGen_3643_ = lean_ctor_get(v___x_3638_, 3);
v_traceState_3644_ = lean_ctor_get(v___x_3638_, 4);
v_messages_3645_ = lean_ctor_get(v___x_3638_, 6);
v_infoState_3646_ = lean_ctor_get(v___x_3638_, 7);
v_snapshotTasks_3647_ = lean_ctor_get(v___x_3638_, 8);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3660_ == 0)
{
lean_object* v_unused_3661_; 
v_unused_3661_ = lean_ctor_get(v___x_3638_, 5);
lean_dec(v_unused_3661_);
v___x_3649_ = v___x_3638_;
v_isShared_3650_ = v_isSharedCheck_3660_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_snapshotTasks_3647_);
lean_inc(v_infoState_3646_);
lean_inc(v_messages_3645_);
lean_inc(v_traceState_3644_);
lean_inc(v_auxDeclNGen_3643_);
lean_inc(v_ngen_3642_);
lean_inc(v_nextMacroScope_3641_);
lean_inc(v_env_3640_);
lean_dec(v___x_3638_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3660_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v_asyncMode_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3655_; 
v_asyncMode_3651_ = lean_ctor_get(v_toEnvExtension_3639_, 2);
v___x_3652_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3633_, v_env_3640_, v_entry_3632_, v_asyncMode_3651_, v___x_3635_);
v___x_3653_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 5, v___x_3653_);
lean_ctor_set(v___x_3649_, 0, v___x_3652_);
v___x_3655_ = v___x_3649_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3652_);
lean_ctor_set(v_reuseFailAlloc_3659_, 1, v_nextMacroScope_3641_);
lean_ctor_set(v_reuseFailAlloc_3659_, 2, v_ngen_3642_);
lean_ctor_set(v_reuseFailAlloc_3659_, 3, v_auxDeclNGen_3643_);
lean_ctor_set(v_reuseFailAlloc_3659_, 4, v_traceState_3644_);
lean_ctor_set(v_reuseFailAlloc_3659_, 5, v___x_3653_);
lean_ctor_set(v_reuseFailAlloc_3659_, 6, v_messages_3645_);
lean_ctor_set(v_reuseFailAlloc_3659_, 7, v_infoState_3646_);
lean_ctor_set(v_reuseFailAlloc_3659_, 8, v_snapshotTasks_3647_);
v___x_3655_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3656_ = lean_st_ref_set(v___y_3637_, v___x_3655_);
v___x_3657_ = lean_box(0);
v___x_3658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3657_);
return v___x_3658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object* v_mod_3702_, lean_object* v_isMeta_3703_, lean_object* v_hint_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
uint8_t v_isMeta_boxed_3708_; lean_object* v_res_3709_; 
v_isMeta_boxed_3708_ = lean_unbox(v_isMeta_3703_);
v_res_3709_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_mod_3702_, v_isMeta_boxed_3708_, v_hint_3704_, v___y_3705_, v___y_3706_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
return v_res_3709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object* v___x_3710_, lean_object* v_declName_3711_, lean_object* v_as_3712_, size_t v_sz_3713_, size_t v_i_3714_, lean_object* v_b_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
uint8_t v___x_3719_; 
v___x_3719_ = lean_usize_dec_lt(v_i_3714_, v_sz_3713_);
if (v___x_3719_ == 0)
{
lean_object* v___x_3720_; 
lean_dec(v_declName_3711_);
v___x_3720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3720_, 0, v_b_3715_);
return v___x_3720_;
}
else
{
lean_object* v___x_3721_; lean_object* v_modules_3722_; lean_object* v___x_3723_; lean_object* v_a_3724_; lean_object* v___x_3725_; lean_object* v_toImport_3726_; lean_object* v_module_3727_; uint8_t v___x_3728_; lean_object* v___x_3729_; 
v___x_3721_ = l_Lean_Environment_header(v___x_3710_);
v_modules_3722_ = lean_ctor_get(v___x_3721_, 3);
lean_inc_ref(v_modules_3722_);
lean_dec_ref(v___x_3721_);
v___x_3723_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3724_ = lean_array_uget_borrowed(v_as_3712_, v_i_3714_);
v___x_3725_ = lean_array_get(v___x_3723_, v_modules_3722_, v_a_3724_);
lean_dec_ref(v_modules_3722_);
v_toImport_3726_ = lean_ctor_get(v___x_3725_, 0);
lean_inc_ref(v_toImport_3726_);
lean_dec(v___x_3725_);
v_module_3727_ = lean_ctor_get(v_toImport_3726_, 0);
lean_inc(v_module_3727_);
lean_dec_ref(v_toImport_3726_);
v___x_3728_ = 0;
lean_inc(v_declName_3711_);
v___x_3729_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3727_, v___x_3728_, v_declName_3711_, v___y_3716_, v___y_3717_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v___x_3730_; size_t v___x_3731_; size_t v___x_3732_; 
lean_dec_ref_known(v___x_3729_, 1);
v___x_3730_ = lean_box(0);
v___x_3731_ = ((size_t)1ULL);
v___x_3732_ = lean_usize_add(v_i_3714_, v___x_3731_);
v_i_3714_ = v___x_3732_;
v_b_3715_ = v___x_3730_;
goto _start;
}
else
{
lean_dec(v_declName_3711_);
return v___x_3729_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object* v___x_3734_, lean_object* v_declName_3735_, lean_object* v_as_3736_, lean_object* v_sz_3737_, lean_object* v_i_3738_, lean_object* v_b_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
size_t v_sz_boxed_3743_; size_t v_i_boxed_3744_; lean_object* v_res_3745_; 
v_sz_boxed_3743_ = lean_unbox_usize(v_sz_3737_);
lean_dec(v_sz_3737_);
v_i_boxed_3744_ = lean_unbox_usize(v_i_3738_);
lean_dec(v_i_3738_);
v_res_3745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v___x_3734_, v_declName_3735_, v_as_3736_, v_sz_boxed_3743_, v_i_boxed_3744_, v_b_3739_, v___y_3740_, v___y_3741_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
lean_dec_ref(v_as_3736_);
lean_dec_ref(v___x_3734_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object* v_declName_3746_, uint8_t v_isMeta_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v___x_3751_; lean_object* v_env_3755_; lean_object* v___y_3757_; lean_object* v___x_3770_; 
v___x_3751_ = lean_st_ref_get(v___y_3749_);
v_env_3755_ = lean_ctor_get(v___x_3751_, 0);
lean_inc_ref(v_env_3755_);
lean_dec(v___x_3751_);
v___x_3770_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3755_, v_declName_3746_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_dec_ref(v_env_3755_);
lean_dec(v_declName_3746_);
goto v___jp_3752_;
}
else
{
lean_object* v_val_3771_; lean_object* v___x_3772_; lean_object* v_modules_3773_; lean_object* v___x_3774_; uint8_t v___x_3775_; 
v_val_3771_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_val_3771_);
lean_dec_ref_known(v___x_3770_, 1);
v___x_3772_ = l_Lean_Environment_header(v_env_3755_);
v_modules_3773_ = lean_ctor_get(v___x_3772_, 3);
lean_inc_ref(v_modules_3773_);
lean_dec_ref(v___x_3772_);
v___x_3774_ = lean_array_get_size(v_modules_3773_);
v___x_3775_ = lean_nat_dec_lt(v_val_3771_, v___x_3774_);
if (v___x_3775_ == 0)
{
lean_dec_ref(v_modules_3773_);
lean_dec(v_val_3771_);
lean_dec_ref(v_env_3755_);
lean_dec(v_declName_3746_);
goto v___jp_3752_;
}
else
{
lean_object* v___x_3776_; lean_object* v_env_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; uint8_t v___y_3781_; 
v___x_3776_ = lean_st_ref_get(v___y_3749_);
v_env_3777_ = lean_ctor_get(v___x_3776_, 0);
lean_inc_ref(v_env_3777_);
lean_dec(v___x_3776_);
v___x_3778_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2);
v___x_3779_ = lean_array_fget(v_modules_3773_, v_val_3771_);
lean_dec(v_val_3771_);
lean_dec_ref(v_modules_3773_);
if (v_isMeta_3747_ == 0)
{
lean_dec_ref(v_env_3777_);
v___y_3781_ = v_isMeta_3747_;
goto v___jp_3780_;
}
else
{
uint8_t v___x_3792_; 
lean_inc(v_declName_3746_);
v___x_3792_ = l_Lean_isMarkedMeta(v_env_3777_, v_declName_3746_);
if (v___x_3792_ == 0)
{
v___y_3781_ = v_isMeta_3747_;
goto v___jp_3780_;
}
else
{
uint8_t v___x_3793_; 
v___x_3793_ = 0;
v___y_3781_ = v___x_3793_;
goto v___jp_3780_;
}
}
v___jp_3780_:
{
lean_object* v_toImport_3782_; lean_object* v_module_3783_; lean_object* v___x_3784_; 
v_toImport_3782_ = lean_ctor_get(v___x_3779_, 0);
lean_inc_ref(v_toImport_3782_);
lean_dec(v___x_3779_);
v_module_3783_ = lean_ctor_get(v_toImport_3782_, 0);
lean_inc(v_module_3783_);
lean_dec_ref(v_toImport_3782_);
lean_inc(v_declName_3746_);
v___x_3784_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3783_, v___y_3781_, v_declName_3746_, v___y_3748_, v___y_3749_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
lean_dec_ref_known(v___x_3784_, 1);
v___x_3785_ = l_Lean_indirectModUseExt;
v___x_3786_ = lean_box(1);
v___x_3787_ = lean_box(0);
lean_inc_ref(v_env_3755_);
v___x_3788_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3778_, v___x_3785_, v_env_3755_, v___x_3786_, v___x_3787_);
v___x_3789_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3788_, v_declName_3746_);
lean_dec(v___x_3788_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v___x_3790_; 
v___x_3790_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3));
v___y_3757_ = v___x_3790_;
goto v___jp_3756_;
}
else
{
lean_object* v_val_3791_; 
v_val_3791_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_val_3791_);
lean_dec_ref_known(v___x_3789_, 1);
v___y_3757_ = v_val_3791_;
goto v___jp_3756_;
}
}
else
{
lean_dec_ref(v_env_3755_);
lean_dec(v_declName_3746_);
return v___x_3784_;
}
}
}
}
v___jp_3752_:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3753_ = lean_box(0);
v___x_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3753_);
return v___x_3754_;
}
v___jp_3756_:
{
lean_object* v___x_3758_; size_t v_sz_3759_; size_t v___x_3760_; lean_object* v___x_3761_; 
v___x_3758_ = lean_box(0);
v_sz_3759_ = lean_array_size(v___y_3757_);
v___x_3760_ = ((size_t)0ULL);
v___x_3761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v_env_3755_, v_declName_3746_, v___y_3757_, v_sz_3759_, v___x_3760_, v___x_3758_, v___y_3748_, v___y_3749_);
lean_dec_ref(v___y_3757_);
lean_dec_ref(v_env_3755_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3768_ == 0)
{
lean_object* v_unused_3769_; 
v_unused_3769_ = lean_ctor_get(v___x_3761_, 0);
lean_dec(v_unused_3769_);
v___x_3763_ = v___x_3761_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_dec(v___x_3761_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 0, v___x_3758_);
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v___x_3758_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
else
{
return v___x_3761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object* v_declName_3794_, lean_object* v_isMeta_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
uint8_t v_isMeta_boxed_3799_; lean_object* v_res_3800_; 
v_isMeta_boxed_3799_ = lean_unbox(v_isMeta_3795_);
v_res_3800_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_declName_3794_, v_isMeta_boxed_3799_, v___y_3796_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object* v_attrName_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_){
_start:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; 
v___x_3805_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_3806_ = lean_st_ref_get(v___x_3805_);
v___x_3807_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3806_, v_attrName_3801_);
lean_dec(v___x_3806_);
if (lean_obj_tag(v___x_3807_) == 1)
{
lean_object* v_val_3808_; lean_object* v_ext_3809_; lean_object* v_name_3810_; uint8_t v___x_3811_; lean_object* v___x_3812_; 
v_val_3808_ = lean_ctor_get(v___x_3807_, 0);
lean_inc(v_val_3808_);
v_ext_3809_ = lean_ctor_get(v_val_3808_, 1);
lean_inc_ref(v_ext_3809_);
lean_dec(v_val_3808_);
v_name_3810_ = lean_ctor_get(v_ext_3809_, 1);
lean_inc(v_name_3810_);
lean_dec_ref(v_ext_3809_);
v___x_3811_ = 1;
v___x_3812_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_name_3810_, v___x_3811_, v_a_3802_, v_a_3803_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3819_ == 0)
{
lean_object* v_unused_3820_; 
v_unused_3820_ = lean_ctor_get(v___x_3812_, 0);
lean_dec(v_unused_3820_);
v___x_3814_ = v___x_3812_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_dec(v___x_3812_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
lean_ctor_set(v___x_3814_, 0, v___x_3807_);
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3807_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
else
{
lean_object* v_a_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3828_; 
lean_dec_ref_known(v___x_3807_, 1);
v_a_3821_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3823_ = v___x_3812_;
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_a_3821_);
lean_dec(v___x_3812_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3826_; 
if (v_isShared_3824_ == 0)
{
v___x_3826_ = v___x_3823_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_a_3821_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
}
}
else
{
lean_object* v___x_3829_; 
v___x_3829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3829_, 0, v___x_3807_);
return v___x_3829_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object* v_attrName_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_){
_start:
{
lean_object* v_res_3834_; 
v_res_3834_ = l_Lean_Meta_Grind_getExtension_x3f(v_attrName_3830_, v_a_3831_, v_a_3832_);
lean_dec(v_a_3832_);
lean_dec_ref(v_a_3831_);
lean_dec(v_attrName_3830_);
return v_res_3834_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerAttr___auto__1(void){
_start:
{
lean_object* v___x_3835_; 
v___x_3835_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_3836_, lean_object* v_x_3837_){
_start:
{
if (lean_obj_tag(v_x_3837_) == 0)
{
return v_x_3836_;
}
else
{
lean_object* v_key_3838_; lean_object* v_value_3839_; lean_object* v_tail_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3866_; 
v_key_3838_ = lean_ctor_get(v_x_3837_, 0);
v_value_3839_ = lean_ctor_get(v_x_3837_, 1);
v_tail_3840_ = lean_ctor_get(v_x_3837_, 2);
v_isSharedCheck_3866_ = !lean_is_exclusive(v_x_3837_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3842_ = v_x_3837_;
v_isShared_3843_ = v_isSharedCheck_3866_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_tail_3840_);
lean_inc(v_value_3839_);
lean_inc(v_key_3838_);
lean_dec(v_x_3837_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3866_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3844_; uint64_t v___y_3846_; 
v___x_3844_ = lean_array_get_size(v_x_3836_);
if (lean_obj_tag(v_key_3838_) == 0)
{
uint64_t v___x_3864_; 
v___x_3864_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_3846_ = v___x_3864_;
goto v___jp_3845_;
}
else
{
uint64_t v_hash_3865_; 
v_hash_3865_ = lean_ctor_get_uint64(v_key_3838_, sizeof(void*)*2);
v___y_3846_ = v_hash_3865_;
goto v___jp_3845_;
}
v___jp_3845_:
{
uint64_t v___x_3847_; uint64_t v___x_3848_; uint64_t v_fold_3849_; uint64_t v___x_3850_; uint64_t v___x_3851_; uint64_t v___x_3852_; size_t v___x_3853_; size_t v___x_3854_; size_t v___x_3855_; size_t v___x_3856_; size_t v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3860_; 
v___x_3847_ = 32ULL;
v___x_3848_ = lean_uint64_shift_right(v___y_3846_, v___x_3847_);
v_fold_3849_ = lean_uint64_xor(v___y_3846_, v___x_3848_);
v___x_3850_ = 16ULL;
v___x_3851_ = lean_uint64_shift_right(v_fold_3849_, v___x_3850_);
v___x_3852_ = lean_uint64_xor(v_fold_3849_, v___x_3851_);
v___x_3853_ = lean_uint64_to_usize(v___x_3852_);
v___x_3854_ = lean_usize_of_nat(v___x_3844_);
v___x_3855_ = ((size_t)1ULL);
v___x_3856_ = lean_usize_sub(v___x_3854_, v___x_3855_);
v___x_3857_ = lean_usize_land(v___x_3853_, v___x_3856_);
v___x_3858_ = lean_array_uget_borrowed(v_x_3836_, v___x_3857_);
lean_inc(v___x_3858_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 2, v___x_3858_);
v___x_3860_ = v___x_3842_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_key_3838_);
lean_ctor_set(v_reuseFailAlloc_3863_, 1, v_value_3839_);
lean_ctor_set(v_reuseFailAlloc_3863_, 2, v___x_3858_);
v___x_3860_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
lean_object* v___x_3861_; 
v___x_3861_ = lean_array_uset(v_x_3836_, v___x_3857_, v___x_3860_);
v_x_3836_ = v___x_3861_;
v_x_3837_ = v_tail_3840_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_3867_, lean_object* v_source_3868_, lean_object* v_target_3869_){
_start:
{
lean_object* v___x_3870_; uint8_t v___x_3871_; 
v___x_3870_ = lean_array_get_size(v_source_3868_);
v___x_3871_ = lean_nat_dec_lt(v_i_3867_, v___x_3870_);
if (v___x_3871_ == 0)
{
lean_dec_ref(v_source_3868_);
lean_dec(v_i_3867_);
return v_target_3869_;
}
else
{
lean_object* v_es_3872_; lean_object* v___x_3873_; lean_object* v_source_3874_; lean_object* v_target_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v_es_3872_ = lean_array_fget(v_source_3868_, v_i_3867_);
v___x_3873_ = lean_box(0);
v_source_3874_ = lean_array_fset(v_source_3868_, v_i_3867_, v___x_3873_);
v_target_3875_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_3869_, v_es_3872_);
v___x_3876_ = lean_unsigned_to_nat(1u);
v___x_3877_ = lean_nat_add(v_i_3867_, v___x_3876_);
lean_dec(v_i_3867_);
v_i_3867_ = v___x_3877_;
v_source_3868_ = v_source_3874_;
v_target_3869_ = v_target_3875_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object* v_data_3879_){
_start:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v_nbuckets_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3880_ = lean_array_get_size(v_data_3879_);
v___x_3881_ = lean_unsigned_to_nat(2u);
v_nbuckets_3882_ = lean_nat_mul(v___x_3880_, v___x_3881_);
v___x_3883_ = lean_unsigned_to_nat(0u);
v___x_3884_ = lean_box(0);
v___x_3885_ = lean_mk_array(v_nbuckets_3882_, v___x_3884_);
v___x_3886_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v___x_3883_, v_data_3879_, v___x_3885_);
return v___x_3886_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object* v_a_3887_, lean_object* v_x_3888_){
_start:
{
if (lean_obj_tag(v_x_3888_) == 0)
{
uint8_t v___x_3889_; 
v___x_3889_ = 0;
return v___x_3889_;
}
else
{
lean_object* v_key_3890_; lean_object* v_tail_3891_; uint8_t v___x_3892_; 
v_key_3890_ = lean_ctor_get(v_x_3888_, 0);
v_tail_3891_ = lean_ctor_get(v_x_3888_, 2);
v___x_3892_ = lean_name_eq(v_key_3890_, v_a_3887_);
if (v___x_3892_ == 0)
{
v_x_3888_ = v_tail_3891_;
goto _start;
}
else
{
return v___x_3892_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_3894_, lean_object* v_x_3895_){
_start:
{
uint8_t v_res_3896_; lean_object* v_r_3897_; 
v_res_3896_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3894_, v_x_3895_);
lean_dec(v_x_3895_);
lean_dec(v_a_3894_);
v_r_3897_ = lean_box(v_res_3896_);
return v_r_3897_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object* v_a_3898_, lean_object* v_b_3899_, lean_object* v_x_3900_){
_start:
{
if (lean_obj_tag(v_x_3900_) == 0)
{
lean_dec(v_b_3899_);
lean_dec(v_a_3898_);
return v_x_3900_;
}
else
{
lean_object* v_key_3901_; lean_object* v_value_3902_; lean_object* v_tail_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3915_; 
v_key_3901_ = lean_ctor_get(v_x_3900_, 0);
v_value_3902_ = lean_ctor_get(v_x_3900_, 1);
v_tail_3903_ = lean_ctor_get(v_x_3900_, 2);
v_isSharedCheck_3915_ = !lean_is_exclusive(v_x_3900_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3905_ = v_x_3900_;
v_isShared_3906_ = v_isSharedCheck_3915_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_tail_3903_);
lean_inc(v_value_3902_);
lean_inc(v_key_3901_);
lean_dec(v_x_3900_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3915_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
uint8_t v___x_3907_; 
v___x_3907_ = lean_name_eq(v_key_3901_, v_a_3898_);
if (v___x_3907_ == 0)
{
lean_object* v___x_3908_; lean_object* v___x_3910_; 
v___x_3908_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3898_, v_b_3899_, v_tail_3903_);
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 2, v___x_3908_);
v___x_3910_ = v___x_3905_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_key_3901_);
lean_ctor_set(v_reuseFailAlloc_3911_, 1, v_value_3902_);
lean_ctor_set(v_reuseFailAlloc_3911_, 2, v___x_3908_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
else
{
lean_object* v___x_3913_; 
lean_dec(v_value_3902_);
lean_dec(v_key_3901_);
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 1, v_b_3899_);
lean_ctor_set(v___x_3905_, 0, v_a_3898_);
v___x_3913_ = v___x_3905_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3898_);
lean_ctor_set(v_reuseFailAlloc_3914_, 1, v_b_3899_);
lean_ctor_set(v_reuseFailAlloc_3914_, 2, v_tail_3903_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object* v_m_3916_, lean_object* v_a_3917_, lean_object* v_b_3918_){
_start:
{
lean_object* v_size_3919_; lean_object* v_buckets_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3966_; 
v_size_3919_ = lean_ctor_get(v_m_3916_, 0);
v_buckets_3920_ = lean_ctor_get(v_m_3916_, 1);
v_isSharedCheck_3966_ = !lean_is_exclusive(v_m_3916_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3922_ = v_m_3916_;
v_isShared_3923_ = v_isSharedCheck_3966_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_buckets_3920_);
lean_inc(v_size_3919_);
lean_dec(v_m_3916_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3966_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3924_; uint64_t v___y_3926_; 
v___x_3924_ = lean_array_get_size(v_buckets_3920_);
if (lean_obj_tag(v_a_3917_) == 0)
{
uint64_t v___x_3964_; 
v___x_3964_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_3926_ = v___x_3964_;
goto v___jp_3925_;
}
else
{
uint64_t v_hash_3965_; 
v_hash_3965_ = lean_ctor_get_uint64(v_a_3917_, sizeof(void*)*2);
v___y_3926_ = v_hash_3965_;
goto v___jp_3925_;
}
v___jp_3925_:
{
uint64_t v___x_3927_; uint64_t v___x_3928_; uint64_t v_fold_3929_; uint64_t v___x_3930_; uint64_t v___x_3931_; uint64_t v___x_3932_; size_t v___x_3933_; size_t v___x_3934_; size_t v___x_3935_; size_t v___x_3936_; size_t v___x_3937_; lean_object* v_bkt_3938_; uint8_t v___x_3939_; 
v___x_3927_ = 32ULL;
v___x_3928_ = lean_uint64_shift_right(v___y_3926_, v___x_3927_);
v_fold_3929_ = lean_uint64_xor(v___y_3926_, v___x_3928_);
v___x_3930_ = 16ULL;
v___x_3931_ = lean_uint64_shift_right(v_fold_3929_, v___x_3930_);
v___x_3932_ = lean_uint64_xor(v_fold_3929_, v___x_3931_);
v___x_3933_ = lean_uint64_to_usize(v___x_3932_);
v___x_3934_ = lean_usize_of_nat(v___x_3924_);
v___x_3935_ = ((size_t)1ULL);
v___x_3936_ = lean_usize_sub(v___x_3934_, v___x_3935_);
v___x_3937_ = lean_usize_land(v___x_3933_, v___x_3936_);
v_bkt_3938_ = lean_array_uget_borrowed(v_buckets_3920_, v___x_3937_);
v___x_3939_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3917_, v_bkt_3938_);
if (v___x_3939_ == 0)
{
lean_object* v___x_3940_; lean_object* v_size_x27_3941_; lean_object* v___x_3942_; lean_object* v_buckets_x27_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; uint8_t v___x_3949_; 
v___x_3940_ = lean_unsigned_to_nat(1u);
v_size_x27_3941_ = lean_nat_add(v_size_3919_, v___x_3940_);
lean_dec(v_size_3919_);
lean_inc(v_bkt_3938_);
v___x_3942_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3942_, 0, v_a_3917_);
lean_ctor_set(v___x_3942_, 1, v_b_3918_);
lean_ctor_set(v___x_3942_, 2, v_bkt_3938_);
v_buckets_x27_3943_ = lean_array_uset(v_buckets_3920_, v___x_3937_, v___x_3942_);
v___x_3944_ = lean_unsigned_to_nat(4u);
v___x_3945_ = lean_nat_mul(v_size_x27_3941_, v___x_3944_);
v___x_3946_ = lean_unsigned_to_nat(3u);
v___x_3947_ = lean_nat_div(v___x_3945_, v___x_3946_);
lean_dec(v___x_3945_);
v___x_3948_ = lean_array_get_size(v_buckets_x27_3943_);
v___x_3949_ = lean_nat_dec_le(v___x_3947_, v___x_3948_);
lean_dec(v___x_3947_);
if (v___x_3949_ == 0)
{
lean_object* v_val_3950_; lean_object* v___x_3952_; 
v_val_3950_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_buckets_x27_3943_);
if (v_isShared_3923_ == 0)
{
lean_ctor_set(v___x_3922_, 1, v_val_3950_);
lean_ctor_set(v___x_3922_, 0, v_size_x27_3941_);
v___x_3952_ = v___x_3922_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_size_x27_3941_);
lean_ctor_set(v_reuseFailAlloc_3953_, 1, v_val_3950_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
else
{
lean_object* v___x_3955_; 
if (v_isShared_3923_ == 0)
{
lean_ctor_set(v___x_3922_, 1, v_buckets_x27_3943_);
lean_ctor_set(v___x_3922_, 0, v_size_x27_3941_);
v___x_3955_ = v___x_3922_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_size_x27_3941_);
lean_ctor_set(v_reuseFailAlloc_3956_, 1, v_buckets_x27_3943_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
}
else
{
lean_object* v___x_3957_; lean_object* v_buckets_x27_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3962_; 
lean_inc(v_bkt_3938_);
v___x_3957_ = lean_box(0);
v_buckets_x27_3958_ = lean_array_uset(v_buckets_3920_, v___x_3937_, v___x_3957_);
v___x_3959_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3917_, v_b_3918_, v_bkt_3938_);
v___x_3960_ = lean_array_uset(v_buckets_x27_3958_, v___x_3937_, v___x_3959_);
if (v_isShared_3923_ == 0)
{
lean_ctor_set(v___x_3922_, 1, v___x_3960_);
v___x_3962_ = v___x_3922_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_size_3919_);
lean_ctor_set(v_reuseFailAlloc_3963_, 1, v___x_3960_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object* v_attrName_3967_, lean_object* v_ref_3968_){
_start:
{
lean_object* v___x_3970_; 
lean_inc(v_ref_3968_);
v___x_3970_ = l_Lean_Meta_Grind_mkExtension(v_ref_3968_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v_a_3971_; uint8_t v___x_3972_; uint8_t v___x_3973_; lean_object* v___x_3974_; 
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
lean_inc_n(v_a_3971_, 2);
lean_dec_ref_known(v___x_3970_, 1);
v___x_3972_ = 0;
v___x_3973_ = 1;
lean_inc(v_ref_3968_);
lean_inc(v_attrName_3967_);
v___x_3974_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3967_, v___x_3972_, v___x_3973_, v_a_3971_, v_ref_3968_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_object* v___x_3975_; 
lean_dec_ref_known(v___x_3974_, 1);
lean_inc(v_ref_3968_);
lean_inc(v_a_3971_);
lean_inc(v_attrName_3967_);
v___x_3975_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3967_, v___x_3972_, v___x_3972_, v_a_3971_, v_ref_3968_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_object* v___x_3976_; 
lean_dec_ref_known(v___x_3975_, 1);
lean_inc(v_ref_3968_);
lean_inc(v_a_3971_);
lean_inc(v_attrName_3967_);
v___x_3976_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3967_, v___x_3973_, v___x_3973_, v_a_3971_, v_ref_3968_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v___x_3977_; 
lean_dec_ref_known(v___x_3976_, 1);
lean_inc(v_a_3971_);
lean_inc(v_attrName_3967_);
v___x_3977_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3967_, v___x_3973_, v___x_3972_, v_a_3971_, v_ref_3968_);
if (lean_obj_tag(v___x_3977_) == 0)
{
lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3988_; 
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_3988_ == 0)
{
lean_object* v_unused_3989_; 
v_unused_3989_ = lean_ctor_get(v___x_3977_, 0);
lean_dec(v_unused_3989_);
v___x_3979_ = v___x_3977_;
v_isShared_3980_ = v_isSharedCheck_3988_;
goto v_resetjp_3978_;
}
else
{
lean_dec(v___x_3977_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3988_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3986_; 
v___x_3981_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_3982_ = lean_st_ref_take(v___x_3981_);
lean_inc(v_a_3971_);
v___x_3983_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v___x_3982_, v_attrName_3967_, v_a_3971_);
v___x_3984_ = lean_st_ref_set(v___x_3981_, v___x_3983_);
if (v_isShared_3980_ == 0)
{
lean_ctor_set(v___x_3979_, 0, v_a_3971_);
v___x_3986_ = v___x_3979_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3971_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
lean_dec(v_a_3971_);
lean_dec(v_attrName_3967_);
v_a_3990_ = lean_ctor_get(v___x_3977_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3977_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3977_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3977_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
else
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4005_; 
lean_dec(v_a_3971_);
lean_dec(v_ref_3968_);
lean_dec(v_attrName_3967_);
v_a_3998_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_4000_ = v___x_3976_;
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3976_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4005_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4003_; 
if (v_isShared_4001_ == 0)
{
v___x_4003_ = v___x_4000_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_a_3998_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
}
else
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
lean_dec(v_a_3971_);
lean_dec(v_ref_3968_);
lean_dec(v_attrName_3967_);
v_a_4006_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_3975_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_3975_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
else
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4021_; 
lean_dec(v_a_3971_);
lean_dec(v_ref_3968_);
lean_dec(v_attrName_3967_);
v_a_4014_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_4016_ = v___x_3974_;
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_3974_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_4014_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
}
}
else
{
lean_dec(v_ref_3968_);
lean_dec(v_attrName_3967_);
return v___x_3970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object* v_attrName_4022_, lean_object* v_ref_4023_, lean_object* v_a_4024_){
_start:
{
lean_object* v_res_4025_; 
v_res_4025_ = l_Lean_Meta_Grind_registerAttr(v_attrName_4022_, v_ref_4023_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object* v_00_u03b2_4026_, lean_object* v_m_4027_, lean_object* v_a_4028_, lean_object* v_b_4029_){
_start:
{
lean_object* v___x_4030_; 
v___x_4030_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v_m_4027_, v_a_4028_, v_b_4029_);
return v___x_4030_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object* v_00_u03b2_4031_, lean_object* v_a_4032_, lean_object* v_x_4033_){
_start:
{
uint8_t v___x_4034_; 
v___x_4034_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4032_, v_x_4033_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4035_, lean_object* v_a_4036_, lean_object* v_x_4037_){
_start:
{
uint8_t v_res_4038_; lean_object* v_r_4039_; 
v_res_4038_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(v_00_u03b2_4035_, v_a_4036_, v_x_4037_);
lean_dec(v_x_4037_);
lean_dec(v_a_4036_);
v_r_4039_ = lean_box(v_res_4038_);
return v_r_4039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object* v_00_u03b2_4040_, lean_object* v_data_4041_){
_start:
{
lean_object* v___x_4042_; 
v___x_4042_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_data_4041_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object* v_00_u03b2_4043_, lean_object* v_a_4044_, lean_object* v_b_4045_, lean_object* v_x_4046_){
_start:
{
lean_object* v___x_4047_; 
v___x_4047_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4044_, v_b_4045_, v_x_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4048_, lean_object* v_i_4049_, lean_object* v_source_4050_, lean_object* v_target_4051_){
_start:
{
lean_object* v___x_4052_; 
v___x_4052_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v_i_4049_, v_source_4050_, v_target_4051_);
return v___x_4052_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4053_, lean_object* v_x_4054_, lean_object* v_x_4055_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_4054_, v_x_4055_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4063_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10));
v___x_4064_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_));
v___x_4065_ = l_Lean_Meta_Grind_registerAttr(v___x_4063_, v___x_4064_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object* v_a_4066_){
_start:
{
lean_object* v_res_4067_; 
v_res_4067_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
return v_res_4067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4078_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_4079_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_4080_ = l_Lean_Meta_Grind_registerAttr(v___x_4078_, v___x_4079_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2____boxed(lean_object* v_a_4081_){
_start:
{
lean_object* v_res_4082_; 
v_res_4082_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
return v_res_4082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object* v_declName_4083_, lean_object* v_a_4084_){
_start:
{
lean_object* v___x_4086_; lean_object* v_env_4087_; lean_object* v___x_4088_; lean_object* v_ext_4089_; lean_object* v_toEnvExtension_4090_; lean_object* v_asyncMode_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v_casesTypes_4094_; uint8_t v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
v___x_4086_ = lean_st_ref_get(v_a_4084_);
v_env_4087_ = lean_ctor_get(v___x_4086_, 0);
lean_inc_ref(v_env_4087_);
lean_dec(v___x_4086_);
v___x_4088_ = l_Lean_Meta_Grind_grindExt;
v_ext_4089_ = lean_ctor_get(v___x_4088_, 1);
v_toEnvExtension_4090_ = lean_ctor_get(v_ext_4089_, 0);
v_asyncMode_4091_ = lean_ctor_get(v_toEnvExtension_4090_, 2);
v___x_4092_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4093_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4092_, v___x_4088_, v_env_4087_, v_asyncMode_4091_);
v_casesTypes_4094_ = lean_ctor_get(v___x_4093_, 0);
lean_inc_ref(v_casesTypes_4094_);
lean_dec(v___x_4093_);
v___x_4095_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_casesTypes_4094_, v_declName_4083_);
lean_dec_ref(v_casesTypes_4094_);
v___x_4096_ = lean_box(v___x_4095_);
v___x_4097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4096_);
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object* v_declName_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_){
_start:
{
lean_object* v_res_4101_; 
v_res_4101_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4098_, v_a_4099_);
lean_dec(v_a_4099_);
lean_dec(v_declName_4098_);
return v_res_4101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object* v_declName_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_){
_start:
{
lean_object* v___x_4106_; 
v___x_4106_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4102_, v_a_4104_);
return v___x_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object* v_declName_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_){
_start:
{
lean_object* v_res_4111_; 
v_res_4111_ = l_Lean_Meta_Grind_isGlobalSplit(v_declName_4107_, v_a_4108_, v_a_4109_);
lean_dec(v_a_4109_);
lean_dec_ref(v_a_4108_);
lean_dec(v_declName_4107_);
return v_res_4111_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Injective(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ExtAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ExtAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_normExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_normExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_extensionMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_extensionMapRef);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_grindExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_grindExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_liaExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_liaExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1 = _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1);
l_Lean_Meta_Grind_registerAttr___auto__1 = _init_l_Lean_Meta_Grind_registerAttr___auto__1();
lean_mark_persistent(l_Lean_Meta_Grind_registerAttr___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Injective(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_ExtAttr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_ExtraModUses(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ExtAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
}
#ifdef __cplusplus
}
#endif
