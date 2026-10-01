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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
uint8_t l_Lean_Meta_Grind_Theorems_contains___redArg(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_mkSimpExt(lean_object*);
lean_object* l_Lean_Meta_addDeclToUnfold(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_addHomoAttr(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addHomoPredAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
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
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindHom"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__46 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value),LEAN_SCALAR_PTR_LITERAL(14, 226, 234, 13, 148, 139, 225, 180)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__47 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "grindHomFallback"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__48 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value),LEAN_SCALAR_PTR_LITERAL(140, 210, 151, 50, 71, 98, 251, 189)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__49 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__49_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "grindHomPred"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__50 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value),LEAN_SCALAR_PTR_LITERAL(1, 153, 163, 64, 153, 27, 218, 140)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__51 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSym"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__52 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__53_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__53_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__53_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value),LEAN_SCALAR_PTR_LITERAL(104, 204, 11, 169, 55, 109, 254, 23)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__53 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__53_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "priority expected"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__54 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__55;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__56 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpPost"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__57 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__57_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__57_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__58 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpPre"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__59 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__59_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__60_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__60_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__60_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__59_value),LEAN_SCALAR_PTR_LITERAL(197, 59, 48, 6, 36, 81, 149, 152)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__60 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__60_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__61 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__61_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__62 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__62_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__63 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__63_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__64 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__64_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__65 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__65_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__66 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__66_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__66_value)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__67 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__67_value;
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 115, .m_capacity = 115, .m_length = 114, .m_data = "\?]` is a helper attribute for displaying inferred patterns, if you want to remove the attribute, consider using `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "]` instead"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14;
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "invalid `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " intro]`, `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "` is not an inductive predicate"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "symbol priorities must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "normalizer must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "declaration to unfold must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "homomorphism rules must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "homomorphism predicates must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
case 10:
{
lean_object* v___x_26_; 
v___x_26_ = lean_unsigned_to_nat(10u);
return v___x_26_;
}
default: 
{
lean_object* v___x_27_; 
v___x_27_ = lean_unsigned_to_nat(11u);
return v___x_27_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___boxed(lean_object* v_x_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Meta_Grind_AttrKind_ctorIdx(v_x_28_);
lean_dec(v_x_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(lean_object* v_t_30_, lean_object* v_k_31_){
_start:
{
switch(lean_obj_tag(v_t_30_))
{
case 0:
{
lean_object* v_k_32_; lean_object* v___x_33_; 
v_k_32_ = lean_ctor_get(v_t_30_, 0);
lean_inc(v_k_32_);
lean_dec_ref_known(v_t_30_, 1);
v___x_33_ = lean_apply_1(v_k_31_, v_k_32_);
return v___x_33_;
}
case 1:
{
uint8_t v_eager_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_eager_34_ = lean_ctor_get_uint8(v_t_30_, 0);
lean_dec_ref_known(v_t_30_, 0);
v___x_35_ = lean_box(v_eager_34_);
v___x_36_ = lean_apply_1(v_k_31_, v___x_35_);
return v___x_36_;
}
case 5:
{
lean_object* v_prio_37_; lean_object* v___x_38_; 
v_prio_37_ = lean_ctor_get(v_t_30_, 0);
lean_inc(v_prio_37_);
lean_dec_ref_known(v_t_30_, 1);
v___x_38_ = lean_apply_1(v_k_31_, v_prio_37_);
return v___x_38_;
}
case 8:
{
uint8_t v_post_39_; uint8_t v_inv_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v_post_39_ = lean_ctor_get_uint8(v_t_30_, 0);
v_inv_40_ = lean_ctor_get_uint8(v_t_30_, 1);
lean_dec_ref_known(v_t_30_, 0);
v___x_41_ = lean_box(v_post_39_);
v___x_42_ = lean_box(v_inv_40_);
v___x_43_ = lean_apply_2(v_k_31_, v___x_41_, v___x_42_);
return v___x_43_;
}
case 10:
{
uint8_t v_fallback_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v_fallback_44_ = lean_ctor_get_uint8(v_t_30_, 0);
lean_dec_ref_known(v_t_30_, 0);
v___x_45_ = lean_box(v_fallback_44_);
v___x_46_ = lean_apply_1(v_k_31_, v___x_45_);
return v___x_46_;
}
default: 
{
lean_dec(v_t_30_);
return v_k_31_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim(lean_object* v_motive_47_, lean_object* v_ctorIdx_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_k_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_49_, v_k_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___boxed(lean_object* v_motive_53_, lean_object* v_ctorIdx_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_k_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Meta_Grind_AttrKind_ctorElim(v_motive_53_, v_ctorIdx_54_, v_t_55_, v_h_56_, v_k_57_);
lean_dec(v_ctorIdx_54_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim___redArg(lean_object* v_t_59_, lean_object* v_ematch_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_59_, v_ematch_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim(lean_object* v_motive_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_ematch_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_63_, v_ematch_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim___redArg(lean_object* v_t_67_, lean_object* v_cases_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_67_, v_cases_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim(lean_object* v_motive_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_cases_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_71_, v_cases_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim___redArg(lean_object* v_t_75_, lean_object* v_intro_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_75_, v_intro_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim(lean_object* v_motive_78_, lean_object* v_t_79_, lean_object* v_h_80_, lean_object* v_intro_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_79_, v_intro_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim___redArg(lean_object* v_t_83_, lean_object* v_infer_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_83_, v_infer_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim(lean_object* v_motive_86_, lean_object* v_t_87_, lean_object* v_h_88_, lean_object* v_infer_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_87_, v_infer_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim___redArg(lean_object* v_t_91_, lean_object* v_ext_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_91_, v_ext_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim(lean_object* v_motive_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_ext_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_95_, v_ext_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim___redArg(lean_object* v_t_99_, lean_object* v_symbol_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_99_, v_symbol_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim(lean_object* v_motive_102_, lean_object* v_t_103_, lean_object* v_h_104_, lean_object* v_symbol_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_103_, v_symbol_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim___redArg(lean_object* v_t_107_, lean_object* v_inj_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_107_, v_inj_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim(lean_object* v_motive_110_, lean_object* v_t_111_, lean_object* v_h_112_, lean_object* v_inj_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_111_, v_inj_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim___redArg(lean_object* v_t_115_, lean_object* v_funCC_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_115_, v_funCC_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim(lean_object* v_motive_118_, lean_object* v_t_119_, lean_object* v_h_120_, lean_object* v_funCC_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_119_, v_funCC_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim___redArg(lean_object* v_t_123_, lean_object* v_norm_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_123_, v_norm_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim(lean_object* v_motive_126_, lean_object* v_t_127_, lean_object* v_h_128_, lean_object* v_norm_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_127_, v_norm_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim___redArg(lean_object* v_t_131_, lean_object* v_unfold_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_131_, v_unfold_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim(lean_object* v_motive_134_, lean_object* v_t_135_, lean_object* v_h_136_, lean_object* v_unfold_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_135_, v_unfold_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim___redArg(lean_object* v_t_139_, lean_object* v_homo_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_139_, v_homo_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homo_elim(lean_object* v_motive_142_, lean_object* v_t_143_, lean_object* v_h_144_, lean_object* v_homo_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_143_, v_homo_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim___redArg(lean_object* v_t_147_, lean_object* v_homoPred_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_147_, v_homoPred_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_homoPred_elim(lean_object* v_motive_150_, lean_object* v_t_151_, lean_object* v_h_152_, lean_object* v_homoPred_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_151_, v_homoPred_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_155_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1);
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
lean_ctor_set(v___x_160_, 2, v___x_159_);
lean_ctor_set(v___x_160_, 3, v___x_159_);
lean_ctor_set(v___x_160_, 4, v___x_158_);
lean_ctor_set(v___x_160_, 5, v___x_158_);
lean_ctor_set(v___x_160_, 6, v___x_158_);
lean_ctor_set(v___x_160_, 7, v___x_158_);
lean_ctor_set(v___x_160_, 8, v___x_158_);
lean_ctor_set(v___x_160_, 9, v___x_158_);
lean_ctor_set(v___x_160_, 10, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_unsigned_to_nat(32u);
v___x_162_ = lean_mk_empty_array_with_capacity(v___x_161_);
v___x_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_164_ = ((size_t)5ULL);
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = lean_unsigned_to_nat(32u);
v___x_167_ = lean_mk_empty_array_with_capacity(v___x_166_);
v___x_168_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_169_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v___x_167_);
lean_ctor_set(v___x_169_, 2, v___x_165_);
lean_ctor_set(v___x_169_, 3, v___x_165_);
lean_ctor_set_usize(v___x_169_, 4, v___x_164_);
return v___x_169_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_170_ = lean_box(1);
v___x_171_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_172_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1);
v___x_173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v___x_171_);
lean_ctor_set(v___x_173_, 2, v___x_170_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(lean_object* v_msgData_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v___x_178_; lean_object* v_toCold_179_; lean_object* v_env_180_; lean_object* v_options_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_178_ = lean_st_ref_get(v___y_176_);
v_toCold_179_ = lean_ctor_get(v___y_175_, 0);
v_env_180_ = lean_ctor_get(v___x_178_, 0);
lean_inc_ref(v_env_180_);
lean_dec(v___x_178_);
v_options_181_ = lean_ctor_get(v_toCold_179_, 2);
v___x_182_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2);
v___x_183_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_181_);
v___x_184_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_184_, 0, v_env_180_);
lean_ctor_set(v___x_184_, 1, v___x_182_);
lean_ctor_set(v___x_184_, 2, v___x_183_);
lean_ctor_set(v___x_184_, 3, v_options_181_);
v___x_185_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v_msgData_174_);
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___boxed(lean_object* v_msgData_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msgData_187_, v___y_188_, v___y_189_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(lean_object* v_msg_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_ref_196_; lean_object* v___x_197_; lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_206_; 
v_ref_196_ = lean_ctor_get(v___y_193_, 2);
v___x_197_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_192_, v___y_193_, v___y_194_);
v_a_198_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_206_ == 0)
{
v___x_200_ = v___x_197_;
v_isShared_201_ = v_isSharedCheck_206_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_197_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_206_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v___x_204_; 
lean_inc(v_ref_196_);
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v_ref_196_);
lean_ctor_set(v___x_202_, 1, v_a_198_);
if (v_isShared_201_ == 0)
{
lean_ctor_set_tag(v___x_200_, 1);
lean_ctor_set(v___x_200_, 0, v___x_202_);
v___x_204_ = v___x_200_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg___boxed(lean_object* v_msg_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_207_, v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(lean_object* v_ref_212_, lean_object* v_msg_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_toCold_217_; lean_object* v_currRecDepth_218_; lean_object* v_ref_219_; uint16_t v_optionFlags_220_; uint8_t v_suppressElabErrors_221_; uint8_t v_isRecordingDeps_222_; lean_object* v_ref_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
v_toCold_217_ = lean_ctor_get(v___y_214_, 0);
v_currRecDepth_218_ = lean_ctor_get(v___y_214_, 1);
v_ref_219_ = lean_ctor_get(v___y_214_, 2);
v_optionFlags_220_ = lean_ctor_get_uint16(v___y_214_, sizeof(void*)*3);
v_suppressElabErrors_221_ = lean_ctor_get_uint8(v___y_214_, sizeof(void*)*3 + 2);
v_isRecordingDeps_222_ = lean_ctor_get_uint8(v___y_214_, sizeof(void*)*3 + 3);
v_ref_223_ = l_Lean_replaceRef(v_ref_212_, v_ref_219_);
lean_inc(v_currRecDepth_218_);
lean_inc_ref(v_toCold_217_);
v___x_224_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_224_, 0, v_toCold_217_);
lean_ctor_set(v___x_224_, 1, v_currRecDepth_218_);
lean_ctor_set(v___x_224_, 2, v_ref_223_);
lean_ctor_set_uint16(v___x_224_, sizeof(void*)*3, v_optionFlags_220_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*3 + 2, v_suppressElabErrors_221_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*3 + 3, v_isRecordingDeps_222_);
v___x_225_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_213_, v___x_224_, v___y_215_);
lean_dec_ref_known(v___x_224_, 3);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg___boxed(lean_object* v_ref_226_, lean_object* v_msg_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_226_, v_msg_227_, v___y_228_, v___y_229_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v_ref_226_);
return v_res_231_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__4));
v___x_242_ = l_Lean_stringToMessageData(v___x_241_);
return v___x_242_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__6));
v___x_245_ = l_Lean_stringToMessageData(v___x_244_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__55(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__54));
v___x_386_ = l_Lean_stringToMessageData(v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object* v_stx_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__3));
lean_inc(v_stx_414_);
v___x_419_ = l_Lean_Syntax_isOfKind(v_stx_414_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_420_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_421_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_420_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_422_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_424_, v_a_415_, v_a_416_);
return v___x_425_;
}
else
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = l_Lean_Syntax_getArg(v_stx_414_, v___x_426_);
v___x_428_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__9));
lean_inc(v___x_427_);
v___x_429_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__11));
lean_inc(v___x_427_);
v___x_431_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__13));
lean_inc(v___x_427_);
v___x_433_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__15));
lean_inc(v___x_427_);
v___x_435_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__17));
lean_inc(v___x_427_);
v___x_437_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__19));
lean_inc(v___x_427_);
v___x_439_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__21));
lean_inc(v___x_427_);
v___x_441_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__23));
lean_inc(v___x_427_);
v___x_443_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__25));
lean_inc(v___x_427_);
v___x_445_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__27));
lean_inc(v___x_427_);
v___x_447_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
lean_inc(v___x_427_);
v___x_449_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__31));
lean_inc(v___x_427_);
v___x_451_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__33));
lean_inc(v___x_427_);
v___x_453_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__35));
lean_inc(v___x_427_);
v___x_455_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__37));
lean_inc(v___x_427_);
v___x_457_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__39));
lean_inc(v___x_427_);
v___x_459_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__41));
lean_inc(v___x_427_);
v___x_461_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_462_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__43));
lean_inc(v___x_427_);
v___x_463_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__45));
lean_inc(v___x_427_);
v___x_465_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__47));
lean_inc(v___x_427_);
v___x_467_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; uint8_t v___x_469_; 
v___x_468_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__49));
lean_inc(v___x_427_);
v___x_469_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__51));
lean_inc(v___x_427_);
v___x_471_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_472_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__53));
lean_inc(v___x_427_);
v___x_473_ = l_Lean_Syntax_isOfKind(v___x_427_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec(v___x_427_);
v___x_474_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_475_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_474_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
v___x_477_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_476_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
v___x_479_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_478_, v_a_415_, v_a_416_);
return v___x_479_;
}
else
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
lean_dec(v_stx_414_);
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = l_Lean_Syntax_getArg(v___x_427_, v___x_480_);
lean_dec(v___x_427_);
v___x_482_ = l_Lean_Syntax_isNatLit_x3f(v___x_481_);
if (lean_obj_tag(v___x_482_) == 1)
{
lean_object* v_val_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_491_; 
lean_dec(v___x_481_);
v_val_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_491_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_491_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_val_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_491_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set_tag(v___x_485_, 5);
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_val_483_);
v___x_488_ = v_reuseFailAlloc_490_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_489_; 
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
}
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; 
lean_dec(v___x_482_);
v___x_492_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__55, &l_Lean_Meta_Grind_getAttrKindCore___closed__55_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__55);
v___x_493_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v___x_481_, v___x_492_, v_a_415_, v_a_416_);
lean_dec(v___x_481_);
return v___x_493_;
}
}
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_494_ = lean_box(11);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_496_ = lean_alloc_ctor(10, 0, 1);
lean_ctor_set_uint8(v___x_496_, 0, v___x_419_);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_498_ = lean_alloc_ctor(10, 0, 1);
lean_ctor_set_uint8(v___x_498_, 0, v___x_465_);
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_500_ = lean_box(9);
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
return v___x_501_;
}
}
else
{
lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_502_ = lean_unsigned_to_nat(1u);
v___x_503_ = l_Lean_Syntax_getArg(v___x_427_, v___x_502_);
lean_inc(v___x_503_);
v___x_504_ = l_Lean_Syntax_matchesNull(v___x_503_, v___x_426_);
if (v___x_504_ == 0)
{
uint8_t v___x_505_; 
lean_inc(v___x_503_);
v___x_505_ = l_Lean_Syntax_matchesNull(v___x_503_, v___x_502_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec(v___x_503_);
lean_dec(v___x_427_);
v___x_506_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_507_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_506_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_508_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
v___x_511_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_510_, v_a_415_, v_a_416_);
return v___x_511_;
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_512_ = l_Lean_Syntax_getArg(v___x_503_, v___x_426_);
lean_dec(v___x_503_);
v___x_513_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__58));
lean_inc(v___x_512_);
v___x_514_ = l_Lean_Syntax_isOfKind(v___x_512_, v___x_513_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__60));
v___x_516_ = l_Lean_Syntax_isOfKind(v___x_512_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec(v___x_427_);
v___x_517_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_518_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_517_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
v___x_520_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_521_, v_a_415_, v_a_416_);
return v___x_522_;
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_523_ = lean_unsigned_to_nat(2u);
v___x_524_ = l_Lean_Syntax_getArg(v___x_427_, v___x_523_);
lean_dec(v___x_427_);
lean_inc(v___x_524_);
v___x_525_ = l_Lean_Syntax_matchesNull(v___x_524_, v___x_426_);
if (v___x_525_ == 0)
{
uint8_t v___x_526_; 
v___x_526_ = l_Lean_Syntax_matchesNull(v___x_524_, v___x_502_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_527_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_528_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_531_, v_a_415_, v_a_416_);
return v___x_532_;
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; 
lean_dec(v_stx_414_);
v___x_533_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_533_, 0, v___x_525_);
lean_ctor_set_uint8(v___x_533_, 1, v___x_419_);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec(v___x_524_);
lean_dec(v_stx_414_);
v___x_535_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_535_, 0, v___x_514_);
lean_ctor_set_uint8(v___x_535_, 1, v___x_514_);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
}
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
lean_dec(v___x_512_);
v___x_537_ = lean_unsigned_to_nat(2u);
v___x_538_ = l_Lean_Syntax_getArg(v___x_427_, v___x_537_);
lean_dec(v___x_427_);
lean_inc(v___x_538_);
v___x_539_ = l_Lean_Syntax_matchesNull(v___x_538_, v___x_426_);
if (v___x_539_ == 0)
{
uint8_t v___x_540_; 
v___x_540_ = l_Lean_Syntax_matchesNull(v___x_538_, v___x_502_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_541_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_542_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_541_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_543_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_545_, v_a_415_, v_a_416_);
return v___x_546_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec(v_stx_414_);
v___x_547_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_547_, 0, v___x_419_);
lean_ctor_set_uint8(v___x_547_, 1, v___x_419_);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
}
else
{
lean_object* v___x_549_; lean_object* v___x_550_; 
lean_dec(v___x_538_);
lean_dec(v_stx_414_);
v___x_549_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_549_, 0, v___x_419_);
lean_ctor_set_uint8(v___x_549_, 1, v___x_504_);
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
}
}
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
lean_dec(v___x_503_);
v___x_551_ = lean_unsigned_to_nat(2u);
v___x_552_ = l_Lean_Syntax_getArg(v___x_427_, v___x_551_);
lean_dec(v___x_427_);
lean_inc(v___x_552_);
v___x_553_ = l_Lean_Syntax_matchesNull(v___x_552_, v___x_426_);
if (v___x_553_ == 0)
{
uint8_t v___x_554_; 
v___x_554_ = l_Lean_Syntax_matchesNull(v___x_552_, v___x_502_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_555_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_556_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_559_, v_a_415_, v_a_416_);
return v___x_560_;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v_stx_414_);
v___x_561_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_561_, 0, v___x_419_);
lean_ctor_set_uint8(v___x_561_, 1, v___x_419_);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec(v___x_552_);
lean_dec(v_stx_414_);
v___x_563_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_563_, 0, v___x_419_);
lean_ctor_set_uint8(v___x_563_, 1, v___x_461_);
v___x_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
return v___x_564_;
}
}
}
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_565_ = lean_box(7);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_567_ = lean_box(6);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_569_ = lean_box(4);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_571_ = lean_box(2);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_573_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_573_, 0, v___x_419_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_575_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_575_, 0, v___x_449_);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_577_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_577_, 0, v___x_419_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_580_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__61));
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_582_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__62));
v___x_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
return v___x_583_;
}
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_584_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__63));
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_586_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__64));
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
return v___x_587_;
}
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_588_ = lean_unsigned_to_nat(3u);
v___x_589_ = l_Lean_Syntax_getArg(v___x_427_, v___x_588_);
lean_dec(v___x_427_);
lean_inc(v___x_589_);
v___x_590_ = l_Lean_Syntax_matchesNull(v___x_589_, v___x_426_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_591_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_589_);
v___x_592_ = l_Lean_Syntax_matchesNull(v___x_589_, v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
lean_dec(v___x_589_);
v___x_593_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_594_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_593_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_595_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_597_, v_a_415_, v_a_416_);
return v___x_598_;
}
else
{
lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_599_ = l_Lean_Syntax_getArg(v___x_589_, v___x_426_);
lean_dec(v___x_589_);
v___x_600_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_601_ = l_Lean_Syntax_isOfKind(v___x_599_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_602_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_603_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_602_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_604_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_606_, v_a_415_, v_a_416_);
return v___x_607_;
}
else
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec(v_stx_414_);
v___x_608_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_608_, 0, v___x_419_);
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
}
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec(v___x_589_);
lean_dec(v_stx_414_);
v___x_611_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_611_, 0, v___x_437_);
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
lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_614_ = lean_unsigned_to_nat(2u);
v___x_615_ = l_Lean_Syntax_getArg(v___x_427_, v___x_614_);
lean_dec(v___x_427_);
lean_inc(v___x_615_);
v___x_616_ = l_Lean_Syntax_matchesNull(v___x_615_, v___x_426_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_615_);
v___x_618_ = l_Lean_Syntax_matchesNull(v___x_615_, v___x_617_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
lean_dec(v___x_615_);
v___x_619_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_620_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_623_, v_a_415_, v_a_416_);
return v___x_624_;
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_625_ = l_Lean_Syntax_getArg(v___x_615_, v___x_426_);
lean_dec(v___x_615_);
v___x_626_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_627_ = l_Lean_Syntax_isOfKind(v___x_625_, v___x_626_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_628_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_629_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
v___x_633_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_632_, v_a_415_, v_a_416_);
return v___x_633_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
lean_dec(v_stx_414_);
v___x_634_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_634_, 0, v___x_419_);
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
return v___x_636_;
}
}
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec(v___x_615_);
lean_dec(v_stx_414_);
v___x_637_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_637_, 0, v___x_435_);
v___x_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
v___x_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
}
}
else
{
lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_640_ = lean_unsigned_to_nat(1u);
v___x_641_ = l_Lean_Syntax_getArg(v___x_427_, v___x_640_);
lean_dec(v___x_427_);
lean_inc(v___x_641_);
v___x_642_ = l_Lean_Syntax_matchesNull(v___x_641_, v___x_426_);
if (v___x_642_ == 0)
{
uint8_t v___x_643_; 
lean_inc(v___x_641_);
v___x_643_ = l_Lean_Syntax_matchesNull(v___x_641_, v___x_640_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec(v___x_641_);
v___x_644_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_645_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v___x_647_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_648_, v_a_415_, v_a_416_);
return v___x_649_;
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_650_ = l_Lean_Syntax_getArg(v___x_641_, v___x_426_);
lean_dec(v___x_641_);
v___x_651_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_652_ = l_Lean_Syntax_isOfKind(v___x_650_, v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_653_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_654_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_653_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_655_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_657_, v_a_415_, v_a_416_);
return v___x_658_;
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
lean_dec(v_stx_414_);
v___x_659_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_659_, 0, v___x_419_);
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
}
}
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
lean_dec(v___x_641_);
lean_dec(v_stx_414_);
v___x_662_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_662_, 0, v___x_433_);
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
return v___x_664_;
}
}
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; 
lean_dec(v___x_427_);
lean_dec(v_stx_414_);
v___x_665_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__65));
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
return v___x_666_;
}
}
else
{
lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_667_ = lean_unsigned_to_nat(1u);
v___x_668_ = l_Lean_Syntax_getArg(v___x_427_, v___x_667_);
lean_dec(v___x_427_);
lean_inc(v___x_668_);
v___x_669_ = l_Lean_Syntax_matchesNull(v___x_668_, v___x_426_);
if (v___x_669_ == 0)
{
uint8_t v___x_670_; 
lean_inc(v___x_668_);
v___x_670_ = l_Lean_Syntax_matchesNull(v___x_668_, v___x_667_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec(v___x_668_);
v___x_671_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_672_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_673_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_675_, v_a_415_, v_a_416_);
return v___x_676_;
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_677_ = l_Lean_Syntax_getArg(v___x_668_, v___x_426_);
lean_dec(v___x_668_);
v___x_678_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_679_ = l_Lean_Syntax_isOfKind(v___x_677_, v___x_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_680_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_681_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_680_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_682_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_684_, v_a_415_, v_a_416_);
return v___x_685_;
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
lean_dec(v_stx_414_);
v___x_686_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_686_, 0, v___x_419_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
}
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
lean_dec(v___x_668_);
lean_dec(v_stx_414_);
v___x_689_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_689_, 0, v___x_429_);
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
return v___x_691_;
}
}
}
else
{
lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_692_ = lean_unsigned_to_nat(1u);
v___x_693_ = l_Lean_Syntax_getArg(v___x_427_, v___x_692_);
lean_dec(v___x_427_);
lean_inc(v___x_693_);
v___x_694_ = l_Lean_Syntax_matchesNull(v___x_693_, v___x_426_);
if (v___x_694_ == 0)
{
uint8_t v___x_695_; 
lean_inc(v___x_693_);
v___x_695_ = l_Lean_Syntax_matchesNull(v___x_693_, v___x_692_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
lean_dec(v___x_693_);
v___x_696_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_697_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_696_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_698_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_700_, v_a_415_, v_a_416_);
return v___x_701_;
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_702_ = l_Lean_Syntax_getArg(v___x_693_, v___x_426_);
lean_dec(v___x_693_);
v___x_703_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_704_ = l_Lean_Syntax_isOfKind(v___x_702_, v___x_703_);
if (v___x_704_ == 0)
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_705_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_706_ = l_Lean_MessageData_ofSyntax(v_stx_414_);
v___x_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_705_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_709_, v_a_415_, v_a_416_);
return v___x_710_;
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
lean_dec(v_stx_414_);
v___x_711_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_711_, 0, v___x_419_);
v___x_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
}
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; 
lean_dec(v___x_693_);
lean_dec(v_stx_414_);
v___x_714_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__67));
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object* v_stx_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Meta_Grind_getAttrKindCore(v_stx_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object* v_00_u03b1_721_, lean_object* v_msg_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_722_, v___y_723_, v___y_724_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object* v_00_u03b1_727_, lean_object* v_msg_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(v_00_u03b1_727_, v_msg_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object* v_00_u03b1_733_, lean_object* v_ref_734_, lean_object* v_msg_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_734_, v_msg_735_, v___y_736_, v___y_737_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object* v_00_u03b1_740_, lean_object* v_ref_741_, lean_object* v_msg_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(v_00_u03b1_740_, v_ref_741_, v_msg_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v_ref_741_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object* v_stx_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_751_ = lean_unsigned_to_nat(1u);
v___x_752_ = l_Lean_Syntax_getArg(v_stx_747_, v___x_751_);
v___x_753_ = l_Lean_Syntax_isNone(v___x_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_754_ = lean_unsigned_to_nat(0u);
v___x_755_ = l_Lean_Syntax_getArg(v___x_752_, v___x_754_);
lean_dec(v___x_752_);
v___x_756_ = l_Lean_Meta_Grind_getAttrKindCore(v___x_755_, v_a_748_, v_a_749_);
return v___x_756_;
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; 
lean_dec(v___x_752_);
v___x_757_ = lean_box(3);
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
return v___x_758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object* v_stx_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_759_, v_a_760_, v_a_761_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_stx_759_);
return v_res_763_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0));
v___x_766_ = l_Lean_stringToMessageData(v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_obj_once(&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1, &l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once, _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1);
v___x_771_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_770_, v_a_767_, v_a_768_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_772_, v_a_773_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object* v_00_u03b1_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_777_, v_a_778_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object* v_00_u03b1_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_Meta_Grind_throwInvalidUsrModifier(v_00_u03b1_781_, v_a_782_, v_a_783_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
return v_res_785_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object* v_ext_790_, lean_object* v_b_791_, uint8_t v_kind_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v_toCold_796_; lean_object* v_currNamespace_797_; lean_object* v___x_798_; lean_object* v_env_799_; lean_object* v_nextMacroScope_800_; lean_object* v_ngen_801_; lean_object* v_auxDeclNGen_802_; lean_object* v_traceState_803_; lean_object* v_recordedDeps_804_; lean_object* v_messages_805_; lean_object* v_infoState_806_; lean_object* v_snapshotTasks_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_819_; 
v_toCold_796_ = lean_ctor_get(v___y_793_, 0);
v_currNamespace_797_ = lean_ctor_get(v_toCold_796_, 4);
v___x_798_ = lean_st_ref_take(v___y_794_);
v_env_799_ = lean_ctor_get(v___x_798_, 0);
v_nextMacroScope_800_ = lean_ctor_get(v___x_798_, 1);
v_ngen_801_ = lean_ctor_get(v___x_798_, 2);
v_auxDeclNGen_802_ = lean_ctor_get(v___x_798_, 3);
v_traceState_803_ = lean_ctor_get(v___x_798_, 4);
v_recordedDeps_804_ = lean_ctor_get(v___x_798_, 6);
v_messages_805_ = lean_ctor_get(v___x_798_, 7);
v_infoState_806_ = lean_ctor_get(v___x_798_, 8);
v_snapshotTasks_807_ = lean_ctor_get(v___x_798_, 9);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v___x_798_, 5);
lean_dec(v_unused_820_);
v___x_809_ = v___x_798_;
v_isShared_810_ = v_isSharedCheck_819_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_snapshotTasks_807_);
lean_inc(v_infoState_806_);
lean_inc(v_messages_805_);
lean_inc(v_recordedDeps_804_);
lean_inc(v_traceState_803_);
lean_inc(v_auxDeclNGen_802_);
lean_inc(v_ngen_801_);
lean_inc(v_nextMacroScope_800_);
lean_inc(v_env_799_);
lean_dec(v___x_798_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_819_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_811_ = lean_box(0);
lean_inc(v_currNamespace_797_);
v___x_812_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_799_, v_ext_790_, v_b_791_, v_kind_792_, v_currNamespace_797_);
v___x_813_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 5, v___x_813_);
lean_ctor_set(v___x_809_, 0, v___x_812_);
v___x_815_ = v___x_809_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_nextMacroScope_800_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v_ngen_801_);
lean_ctor_set(v_reuseFailAlloc_818_, 3, v_auxDeclNGen_802_);
lean_ctor_set(v_reuseFailAlloc_818_, 4, v_traceState_803_);
lean_ctor_set(v_reuseFailAlloc_818_, 5, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_818_, 6, v_recordedDeps_804_);
lean_ctor_set(v_reuseFailAlloc_818_, 7, v_messages_805_);
lean_ctor_set(v_reuseFailAlloc_818_, 8, v_infoState_806_);
lean_ctor_set(v_reuseFailAlloc_818_, 9, v_snapshotTasks_807_);
v___x_815_ = v_reuseFailAlloc_818_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = lean_st_ref_put(v___y_794_, v___x_815_);
v___x_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_811_);
return v___x_817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object* v_ext_821_, lean_object* v_b_822_, lean_object* v_kind_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
uint8_t v_kind_boxed_827_; lean_object* v_res_828_; 
v_kind_boxed_827_ = lean_unbox(v_kind_823_);
v_res_828_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_821_, v_b_822_, v_kind_boxed_827_, v___y_824_, v___y_825_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object* v_00_u03b1_829_, lean_object* v_00_u03b2_830_, lean_object* v_00_u03c3_831_, lean_object* v_ext_832_, lean_object* v_b_833_, uint8_t v_kind_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_832_, v_b_833_, v_kind_834_, v___y_835_, v___y_836_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object* v_00_u03b1_839_, lean_object* v_00_u03b2_840_, lean_object* v_00_u03c3_841_, lean_object* v_ext_842_, lean_object* v_b_843_, lean_object* v_kind_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
uint8_t v_kind_boxed_848_; lean_object* v_res_849_; 
v_kind_boxed_848_ = lean_unbox(v_kind_844_);
v_res_849_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(v_00_u03b1_839_, v_00_u03b2_840_, v_00_u03c3_841_, v_ext_842_, v_b_843_, v_kind_boxed_848_, v___y_845_, v___y_846_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object* v_ext_850_, lean_object* v_declName_851_, uint8_t v_eager_852_, uint8_t v_attrKind_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v___x_857_; 
lean_inc(v_declName_851_);
v___x_857_ = l_Lean_Meta_Grind_validateCasesAttr(v_declName_851_, v_eager_852_, v_a_854_, v_a_855_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec_ref_known(v___x_857_, 1);
v___x_858_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_858_, 0, v_declName_851_);
lean_ctor_set_uint8(v___x_858_, sizeof(void*)*1, v_eager_852_);
v___x_859_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_850_, v___x_858_, v_attrKind_853_, v_a_854_, v_a_855_);
return v___x_859_;
}
else
{
lean_dec(v_declName_851_);
lean_dec_ref(v_ext_850_);
return v___x_857_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object* v_ext_860_, lean_object* v_declName_861_, lean_object* v_eager_862_, lean_object* v_attrKind_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
uint8_t v_eager_boxed_867_; uint8_t v_attrKind_boxed_868_; lean_object* v_res_869_; 
v_eager_boxed_867_ = lean_unbox(v_eager_862_);
v_attrKind_boxed_868_ = lean_unbox(v_attrKind_863_);
v_res_869_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_860_, v_declName_861_, v_eager_boxed_867_, v_attrKind_boxed_868_, v_a_864_, v_a_865_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object* v_ext_870_, lean_object* v_declName_871_, uint8_t v_attrKind_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___x_876_; 
lean_inc(v_declName_871_);
v___x_876_ = l_Lean_Meta_Grind_validateExtAttr(v_declName_871_, v_a_873_, v_a_874_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_884_; 
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; 
v_unused_885_ = lean_ctor_get(v___x_876_, 0);
lean_dec(v_unused_885_);
v___x_878_ = v___x_876_;
v_isShared_879_ = v_isSharedCheck_884_;
goto v_resetjp_877_;
}
else
{
lean_dec(v___x_876_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_884_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v_declName_871_);
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_declName_871_);
v___x_881_ = v_reuseFailAlloc_883_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_870_, v___x_881_, v_attrKind_872_, v_a_873_, v_a_874_);
return v___x_882_;
}
}
}
else
{
lean_dec(v_declName_871_);
lean_dec_ref(v_ext_870_);
return v___x_876_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object* v_ext_886_, lean_object* v_declName_887_, lean_object* v_attrKind_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
uint8_t v_attrKind_boxed_892_; lean_object* v_res_893_; 
v_attrKind_boxed_892_ = lean_unbox(v_attrKind_888_);
v_res_893_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_886_, v_declName_887_, v_attrKind_boxed_892_, v_a_889_, v_a_890_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object* v_ext_894_, lean_object* v_declName_895_, uint8_t v_attrKind_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_900_, 0, v_declName_895_);
v___x_901_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_894_, v___x_900_, v_attrKind_896_, v_a_897_, v_a_898_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object* v_ext_902_, lean_object* v_declName_903_, lean_object* v_attrKind_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
uint8_t v_attrKind_boxed_908_; lean_object* v_res_909_; 
v_attrKind_boxed_908_ = lean_unbox(v_attrKind_904_);
v_res_909_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_902_, v_declName_903_, v_attrKind_boxed_908_, v_a_905_, v_a_906_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object* v_a_910_, lean_object* v_s_911_){
_start:
{
lean_object* v_casesTypes_912_; lean_object* v_funCC_913_; lean_object* v_ematch_914_; lean_object* v_inj_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
v_casesTypes_912_ = lean_ctor_get(v_s_911_, 0);
v_funCC_913_ = lean_ctor_get(v_s_911_, 2);
v_ematch_914_ = lean_ctor_get(v_s_911_, 3);
v_inj_915_ = lean_ctor_get(v_s_911_, 4);
v_isSharedCheck_922_ = !lean_is_exclusive(v_s_911_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; 
v_unused_923_ = lean_ctor_get(v_s_911_, 1);
lean_dec(v_unused_923_);
v___x_917_ = v_s_911_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_inj_915_);
lean_inc(v_ematch_914_);
lean_inc(v_funCC_913_);
lean_inc(v_casesTypes_912_);
lean_dec(v_s_911_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 1, v_a_910_);
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_casesTypes_912_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_a_910_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_funCC_913_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v_ematch_914_);
lean_ctor_set(v_reuseFailAlloc_921_, 4, v_inj_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object* v_ext_924_, lean_object* v_declName_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v_ext_931_; lean_object* v_toEnvExtension_932_; lean_object* v_env_933_; lean_object* v_asyncMode_934_; lean_object* v___x_935_; lean_object* v_extThms_936_; lean_object* v___x_937_; 
v___x_929_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_930_ = lean_st_ref_get(v_a_927_);
v_ext_931_ = lean_ctor_get(v_ext_924_, 1);
v_toEnvExtension_932_ = lean_ctor_get(v_ext_931_, 0);
v_env_933_ = lean_ctor_get(v___x_930_, 0);
lean_inc_ref(v_env_933_);
lean_dec(v___x_930_);
v_asyncMode_934_ = lean_ctor_get(v_toEnvExtension_932_, 2);
v___x_935_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_929_, v_ext_924_, v_env_933_, v_asyncMode_934_);
v_extThms_936_ = lean_ctor_get(v___x_935_, 1);
lean_inc_ref(v_extThms_936_);
lean_dec(v___x_935_);
v___x_937_ = l_Lean_Meta_Grind_ExtTheorems_eraseDecl(v_extThms_936_, v_declName_925_, v_a_926_, v_a_927_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_968_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_968_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_968_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_968_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___f_942_; lean_object* v___x_943_; lean_object* v_env_944_; lean_object* v_nextMacroScope_945_; lean_object* v_ngen_946_; lean_object* v_auxDeclNGen_947_; lean_object* v_traceState_948_; lean_object* v_recordedDeps_949_; lean_object* v_messages_950_; lean_object* v_infoState_951_; lean_object* v_snapshotTasks_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_966_; 
v___f_942_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0), 2, 1);
lean_closure_set(v___f_942_, 0, v_a_938_);
v___x_943_ = lean_st_ref_take(v_a_927_);
v_env_944_ = lean_ctor_get(v___x_943_, 0);
v_nextMacroScope_945_ = lean_ctor_get(v___x_943_, 1);
v_ngen_946_ = lean_ctor_get(v___x_943_, 2);
v_auxDeclNGen_947_ = lean_ctor_get(v___x_943_, 3);
v_traceState_948_ = lean_ctor_get(v___x_943_, 4);
v_recordedDeps_949_ = lean_ctor_get(v___x_943_, 6);
v_messages_950_ = lean_ctor_get(v___x_943_, 7);
v_infoState_951_ = lean_ctor_get(v___x_943_, 8);
v_snapshotTasks_952_ = lean_ctor_get(v___x_943_, 9);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; 
v_unused_967_ = lean_ctor_get(v___x_943_, 5);
lean_dec(v_unused_967_);
v___x_954_ = v___x_943_;
v_isShared_955_ = v_isSharedCheck_966_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_snapshotTasks_952_);
lean_inc(v_infoState_951_);
lean_inc(v_messages_950_);
lean_inc(v_recordedDeps_949_);
lean_inc(v_traceState_948_);
lean_inc(v_auxDeclNGen_947_);
lean_inc(v_ngen_946_);
lean_inc(v_nextMacroScope_945_);
lean_inc(v_env_944_);
lean_dec(v___x_943_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_966_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_956_ = lean_box(0);
v___x_957_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_924_, v_env_944_, v___f_942_);
v___x_958_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 5, v___x_958_);
lean_ctor_set(v___x_954_, 0, v___x_957_);
v___x_960_ = v___x_954_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_nextMacroScope_945_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_ngen_946_);
lean_ctor_set(v_reuseFailAlloc_965_, 3, v_auxDeclNGen_947_);
lean_ctor_set(v_reuseFailAlloc_965_, 4, v_traceState_948_);
lean_ctor_set(v_reuseFailAlloc_965_, 5, v___x_958_);
lean_ctor_set(v_reuseFailAlloc_965_, 6, v_recordedDeps_949_);
lean_ctor_set(v_reuseFailAlloc_965_, 7, v_messages_950_);
lean_ctor_set(v_reuseFailAlloc_965_, 8, v_infoState_951_);
lean_ctor_set(v_reuseFailAlloc_965_, 9, v_snapshotTasks_952_);
v___x_960_ = v_reuseFailAlloc_965_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_961_ = lean_st_ref_put(v_a_927_, v___x_960_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_956_);
v___x_963_ = v___x_940_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_956_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
lean_dec_ref(v_ext_924_);
v_a_969_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_937_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_937_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object* v_ext_977_, lean_object* v_declName_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_977_, v_declName_978_, v_a_979_, v_a_980_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object* v_a_983_, lean_object* v_s_984_){
_start:
{
lean_object* v_extThms_985_; lean_object* v_funCC_986_; lean_object* v_ematch_987_; lean_object* v_inj_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
v_extThms_985_ = lean_ctor_get(v_s_984_, 1);
v_funCC_986_ = lean_ctor_get(v_s_984_, 2);
v_ematch_987_ = lean_ctor_get(v_s_984_, 3);
v_inj_988_ = lean_ctor_get(v_s_984_, 4);
v_isSharedCheck_995_ = !lean_is_exclusive(v_s_984_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; 
v_unused_996_ = lean_ctor_get(v_s_984_, 0);
lean_dec(v_unused_996_);
v___x_990_ = v_s_984_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_inj_988_);
lean_inc(v_ematch_987_);
lean_inc(v_funCC_986_);
lean_inc(v_extThms_985_);
lean_dec(v_s_984_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v_a_983_);
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_983_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_extThms_985_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_funCC_986_);
lean_ctor_set(v_reuseFailAlloc_994_, 3, v_ematch_987_);
lean_ctor_set(v_reuseFailAlloc_994_, 4, v_inj_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object* v_ext_997_, lean_object* v_declName_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_inc(v_declName_998_);
v___x_1003_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_998_, v_a_999_, v_a_1000_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v___x_1004_; lean_object* v_ext_1005_; lean_object* v_toEnvExtension_1006_; lean_object* v_env_1007_; lean_object* v_asyncMode_1008_; lean_object* v___x_1009_; lean_object* v_casesTypes_1010_; lean_object* v___x_1011_; 
lean_dec_ref_known(v___x_1003_, 1);
v___x_1004_ = lean_st_ref_get(v_a_1000_);
v_ext_1005_ = lean_ctor_get(v_ext_997_, 1);
v_toEnvExtension_1006_ = lean_ctor_get(v_ext_1005_, 0);
v_env_1007_ = lean_ctor_get(v___x_1004_, 0);
lean_inc_ref(v_env_1007_);
lean_dec(v___x_1004_);
v_asyncMode_1008_ = lean_ctor_get(v_toEnvExtension_1006_, 2);
v___x_1009_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1002_, v_ext_997_, v_env_1007_, v_asyncMode_1008_);
v_casesTypes_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc_ref(v_casesTypes_1010_);
lean_dec(v___x_1009_);
v___x_1011_ = l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_casesTypes_1010_, v_declName_998_, v_a_999_, v_a_1000_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1042_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1014_ = v___x_1011_;
v_isShared_1015_ = v_isSharedCheck_1042_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1011_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1042_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___f_1016_; lean_object* v___x_1017_; lean_object* v_env_1018_; lean_object* v_nextMacroScope_1019_; lean_object* v_ngen_1020_; lean_object* v_auxDeclNGen_1021_; lean_object* v_traceState_1022_; lean_object* v_recordedDeps_1023_; lean_object* v_messages_1024_; lean_object* v_infoState_1025_; lean_object* v_snapshotTasks_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1040_; 
v___f_1016_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0), 2, 1);
lean_closure_set(v___f_1016_, 0, v_a_1012_);
v___x_1017_ = lean_st_ref_take(v_a_1000_);
v_env_1018_ = lean_ctor_get(v___x_1017_, 0);
v_nextMacroScope_1019_ = lean_ctor_get(v___x_1017_, 1);
v_ngen_1020_ = lean_ctor_get(v___x_1017_, 2);
v_auxDeclNGen_1021_ = lean_ctor_get(v___x_1017_, 3);
v_traceState_1022_ = lean_ctor_get(v___x_1017_, 4);
v_recordedDeps_1023_ = lean_ctor_get(v___x_1017_, 6);
v_messages_1024_ = lean_ctor_get(v___x_1017_, 7);
v_infoState_1025_ = lean_ctor_get(v___x_1017_, 8);
v_snapshotTasks_1026_ = lean_ctor_get(v___x_1017_, 9);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1040_ == 0)
{
lean_object* v_unused_1041_; 
v_unused_1041_ = lean_ctor_get(v___x_1017_, 5);
lean_dec(v_unused_1041_);
v___x_1028_ = v___x_1017_;
v_isShared_1029_ = v_isSharedCheck_1040_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_snapshotTasks_1026_);
lean_inc(v_infoState_1025_);
lean_inc(v_messages_1024_);
lean_inc(v_recordedDeps_1023_);
lean_inc(v_traceState_1022_);
lean_inc(v_auxDeclNGen_1021_);
lean_inc(v_ngen_1020_);
lean_inc(v_nextMacroScope_1019_);
lean_inc(v_env_1018_);
lean_dec(v___x_1017_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1040_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1030_ = lean_box(0);
v___x_1031_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_997_, v_env_1018_, v___f_1016_);
v___x_1032_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 5, v___x_1032_);
lean_ctor_set(v___x_1028_, 0, v___x_1031_);
v___x_1034_ = v___x_1028_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_nextMacroScope_1019_);
lean_ctor_set(v_reuseFailAlloc_1039_, 2, v_ngen_1020_);
lean_ctor_set(v_reuseFailAlloc_1039_, 3, v_auxDeclNGen_1021_);
lean_ctor_set(v_reuseFailAlloc_1039_, 4, v_traceState_1022_);
lean_ctor_set(v_reuseFailAlloc_1039_, 5, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1039_, 6, v_recordedDeps_1023_);
lean_ctor_set(v_reuseFailAlloc_1039_, 7, v_messages_1024_);
lean_ctor_set(v_reuseFailAlloc_1039_, 8, v_infoState_1025_);
lean_ctor_set(v_reuseFailAlloc_1039_, 9, v_snapshotTasks_1026_);
v___x_1034_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1035_ = lean_st_ref_put(v_a_1000_, v___x_1034_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1030_);
v___x_1037_ = v___x_1014_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1030_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_dec_ref(v_ext_997_);
v_a_1043_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1011_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1011_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
else
{
lean_dec(v_declName_998_);
lean_dec_ref(v_ext_997_);
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object* v_ext_1051_, lean_object* v_declName_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_1051_, v_declName_1052_, v_a_1053_, v_a_1054_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object* v___x_1057_, lean_object* v_s_1058_){
_start:
{
lean_object* v_casesTypes_1059_; lean_object* v_extThms_1060_; lean_object* v_ematch_1061_; lean_object* v_inj_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
v_casesTypes_1059_ = lean_ctor_get(v_s_1058_, 0);
v_extThms_1060_ = lean_ctor_get(v_s_1058_, 1);
v_ematch_1061_ = lean_ctor_get(v_s_1058_, 3);
v_inj_1062_ = lean_ctor_get(v_s_1058_, 4);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_s_1058_);
if (v_isSharedCheck_1069_ == 0)
{
lean_object* v_unused_1070_; 
v_unused_1070_ = lean_ctor_get(v_s_1058_, 2);
lean_dec(v_unused_1070_);
v___x_1064_ = v_s_1058_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_inj_1062_);
lean_inc(v_ematch_1061_);
lean_inc(v_extThms_1060_);
lean_inc(v_casesTypes_1059_);
lean_dec(v_s_1058_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 2, v___x_1057_);
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_casesTypes_1059_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_extThms_1060_);
lean_ctor_set(v_reuseFailAlloc_1068_, 2, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1068_, 3, v_ematch_1061_);
lean_ctor_set(v_reuseFailAlloc_1068_, 4, v_inj_1062_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object* v_k_1071_, lean_object* v_t_1072_){
_start:
{
if (lean_obj_tag(v_t_1072_) == 0)
{
lean_object* v_k_1073_; lean_object* v_v_1074_; lean_object* v_l_1075_; lean_object* v_r_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1730_; 
v_k_1073_ = lean_ctor_get(v_t_1072_, 1);
v_v_1074_ = lean_ctor_get(v_t_1072_, 2);
v_l_1075_ = lean_ctor_get(v_t_1072_, 3);
v_r_1076_ = lean_ctor_get(v_t_1072_, 4);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_t_1072_);
if (v_isSharedCheck_1730_ == 0)
{
lean_object* v_unused_1731_; 
v_unused_1731_ = lean_ctor_get(v_t_1072_, 0);
lean_dec(v_unused_1731_);
v___x_1078_ = v_t_1072_;
v_isShared_1079_ = v_isSharedCheck_1730_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_r_1076_);
lean_inc(v_l_1075_);
lean_inc(v_v_1074_);
lean_inc(v_k_1073_);
lean_dec(v_t_1072_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1730_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
uint8_t v___x_1080_; 
v___x_1080_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1071_, v_k_1073_);
switch(v___x_1080_)
{
case 0:
{
lean_object* v_impl_1081_; lean_object* v___x_1082_; 
v_impl_1081_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1071_, v_l_1075_);
v___x_1082_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1081_) == 0)
{
if (lean_obj_tag(v_r_1076_) == 0)
{
lean_object* v_size_1083_; lean_object* v_size_1084_; lean_object* v_k_1085_; lean_object* v_v_1086_; lean_object* v_l_1087_; lean_object* v_r_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v_size_1083_ = lean_ctor_get(v_impl_1081_, 0);
v_size_1084_ = lean_ctor_get(v_r_1076_, 0);
v_k_1085_ = lean_ctor_get(v_r_1076_, 1);
v_v_1086_ = lean_ctor_get(v_r_1076_, 2);
v_l_1087_ = lean_ctor_get(v_r_1076_, 3);
lean_inc(v_l_1087_);
v_r_1088_ = lean_ctor_get(v_r_1076_, 4);
v___x_1089_ = lean_unsigned_to_nat(3u);
v___x_1090_ = lean_nat_mul(v___x_1089_, v_size_1083_);
v___x_1091_ = lean_nat_dec_lt(v___x_1090_, v_size_1084_);
lean_dec(v___x_1090_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1095_; 
lean_dec(v_l_1087_);
v___x_1092_ = lean_nat_add(v___x_1082_, v_size_1083_);
v___x_1093_ = lean_nat_add(v___x_1092_, v_size_1084_);
lean_dec(v___x_1092_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 3, v_impl_1081_);
lean_ctor_set(v___x_1078_, 0, v___x_1093_);
v___x_1095_ = v___x_1078_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_k_1073_);
lean_ctor_set(v_reuseFailAlloc_1096_, 2, v_v_1074_);
lean_ctor_set(v_reuseFailAlloc_1096_, 3, v_impl_1081_);
lean_ctor_set(v_reuseFailAlloc_1096_, 4, v_r_1076_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
else
{
lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1160_; 
lean_inc(v_r_1088_);
lean_inc(v_v_1086_);
lean_inc(v_k_1085_);
lean_inc(v_size_1084_);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_r_1076_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; lean_object* v_unused_1162_; lean_object* v_unused_1163_; lean_object* v_unused_1164_; lean_object* v_unused_1165_; 
v_unused_1161_ = lean_ctor_get(v_r_1076_, 4);
lean_dec(v_unused_1161_);
v_unused_1162_ = lean_ctor_get(v_r_1076_, 3);
lean_dec(v_unused_1162_);
v_unused_1163_ = lean_ctor_get(v_r_1076_, 2);
lean_dec(v_unused_1163_);
v_unused_1164_ = lean_ctor_get(v_r_1076_, 1);
lean_dec(v_unused_1164_);
v_unused_1165_ = lean_ctor_get(v_r_1076_, 0);
lean_dec(v_unused_1165_);
v___x_1098_ = v_r_1076_;
v_isShared_1099_ = v_isSharedCheck_1160_;
goto v_resetjp_1097_;
}
else
{
lean_dec(v_r_1076_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1160_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v_size_1100_; lean_object* v_k_1101_; lean_object* v_v_1102_; lean_object* v_l_1103_; lean_object* v_r_1104_; lean_object* v_size_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v_size_1100_ = lean_ctor_get(v_l_1087_, 0);
v_k_1101_ = lean_ctor_get(v_l_1087_, 1);
v_v_1102_ = lean_ctor_get(v_l_1087_, 2);
v_l_1103_ = lean_ctor_get(v_l_1087_, 3);
v_r_1104_ = lean_ctor_get(v_l_1087_, 4);
v_size_1105_ = lean_ctor_get(v_r_1088_, 0);
v___x_1106_ = lean_unsigned_to_nat(2u);
v___x_1107_ = lean_nat_mul(v___x_1106_, v_size_1105_);
v___x_1108_ = lean_nat_dec_lt(v_size_1100_, v___x_1107_);
lean_dec(v___x_1107_);
if (v___x_1108_ == 0)
{
lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1136_; 
lean_inc(v_r_1104_);
lean_inc(v_l_1103_);
lean_inc(v_v_1102_);
lean_inc(v_k_1101_);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_l_1087_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; lean_object* v_unused_1138_; lean_object* v_unused_1139_; lean_object* v_unused_1140_; lean_object* v_unused_1141_; 
v_unused_1137_ = lean_ctor_get(v_l_1087_, 4);
lean_dec(v_unused_1137_);
v_unused_1138_ = lean_ctor_get(v_l_1087_, 3);
lean_dec(v_unused_1138_);
v_unused_1139_ = lean_ctor_get(v_l_1087_, 2);
lean_dec(v_unused_1139_);
v_unused_1140_ = lean_ctor_get(v_l_1087_, 1);
lean_dec(v_unused_1140_);
v_unused_1141_ = lean_ctor_get(v_l_1087_, 0);
lean_dec(v_unused_1141_);
v___x_1110_ = v_l_1087_;
v_isShared_1111_ = v_isSharedCheck_1136_;
goto v_resetjp_1109_;
}
else
{
lean_dec(v_l_1087_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1136_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1126_; 
v___x_1112_ = lean_nat_add(v___x_1082_, v_size_1083_);
v___x_1113_ = lean_nat_add(v___x_1112_, v_size_1084_);
lean_dec(v_size_1084_);
if (lean_obj_tag(v_l_1103_) == 0)
{
lean_object* v_size_1134_; 
v_size_1134_ = lean_ctor_get(v_l_1103_, 0);
lean_inc(v_size_1134_);
v___y_1126_ = v_size_1134_;
goto v___jp_1125_;
}
else
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_unsigned_to_nat(0u);
v___y_1126_ = v___x_1135_;
goto v___jp_1125_;
}
v___jp_1114_:
{
lean_object* v___x_1118_; lean_object* v___x_1120_; 
v___x_1118_ = lean_nat_add(v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec(v___y_1116_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 4, v_r_1088_);
lean_ctor_set(v___x_1110_, 3, v_r_1104_);
lean_ctor_set(v___x_1110_, 2, v_v_1086_);
lean_ctor_set(v___x_1110_, 1, v_k_1085_);
lean_ctor_set(v___x_1110_, 0, v___x_1118_);
v___x_1120_ = v___x_1110_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_k_1085_);
lean_ctor_set(v_reuseFailAlloc_1124_, 2, v_v_1086_);
lean_ctor_set(v_reuseFailAlloc_1124_, 3, v_r_1104_);
lean_ctor_set(v_reuseFailAlloc_1124_, 4, v_r_1088_);
v___x_1120_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1122_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 4, v___x_1120_);
lean_ctor_set(v___x_1098_, 3, v___y_1115_);
lean_ctor_set(v___x_1098_, 2, v_v_1102_);
lean_ctor_set(v___x_1098_, 1, v_k_1101_);
lean_ctor_set(v___x_1098_, 0, v___x_1113_);
v___x_1122_ = v___x_1098_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_k_1101_);
lean_ctor_set(v_reuseFailAlloc_1123_, 2, v_v_1102_);
lean_ctor_set(v_reuseFailAlloc_1123_, 3, v___y_1115_);
lean_ctor_set(v_reuseFailAlloc_1123_, 4, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
v___jp_1125_:
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1127_ = lean_nat_add(v___x_1112_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec(v___x_1112_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 4, v_l_1103_);
lean_ctor_set(v___x_1078_, 3, v_impl_1081_);
lean_ctor_set(v___x_1078_, 0, v___x_1127_);
v___x_1129_ = v___x_1078_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_k_1073_);
lean_ctor_set(v_reuseFailAlloc_1133_, 2, v_v_1074_);
lean_ctor_set(v_reuseFailAlloc_1133_, 3, v_impl_1081_);
lean_ctor_set(v_reuseFailAlloc_1133_, 4, v_l_1103_);
v___x_1129_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_nat_add(v___x_1082_, v_size_1105_);
if (lean_obj_tag(v_r_1104_) == 0)
{
lean_object* v_size_1131_; 
v_size_1131_ = lean_ctor_get(v_r_1104_, 0);
lean_inc(v_size_1131_);
v___y_1115_ = v___x_1129_;
v___y_1116_ = v___x_1130_;
v___y_1117_ = v_size_1131_;
goto v___jp_1114_;
}
else
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_unsigned_to_nat(0u);
v___y_1115_ = v___x_1129_;
v___y_1116_ = v___x_1130_;
v___y_1117_ = v___x_1132_;
goto v___jp_1114_;
}
}
}
}
}
else
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
lean_del_object(v___x_1078_);
v___x_1142_ = lean_nat_add(v___x_1082_, v_size_1083_);
v___x_1143_ = lean_nat_add(v___x_1142_, v_size_1084_);
lean_dec(v_size_1084_);
v___x_1144_ = lean_nat_add(v___x_1142_, v_size_1100_);
lean_dec(v___x_1142_);
lean_inc_ref(v_impl_1081_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 4, v_l_1087_);
lean_ctor_set(v___x_1098_, 3, v_impl_1081_);
lean_ctor_set(v___x_1098_, 2, v_v_1074_);
lean_ctor_set(v___x_1098_, 1, v_k_1073_);
lean_ctor_set(v___x_1098_, 0, v___x_1144_);
v___x_1146_ = v___x_1098_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_k_1073_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_v_1074_);
lean_ctor_set(v_reuseFailAlloc_1159_, 3, v_impl_1081_);
lean_ctor_set(v_reuseFailAlloc_1159_, 4, v_l_1087_);
v___x_1146_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
v_isSharedCheck_1153_ = !lean_is_exclusive(v_impl_1081_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; lean_object* v_unused_1155_; lean_object* v_unused_1156_; lean_object* v_unused_1157_; lean_object* v_unused_1158_; 
v_unused_1154_ = lean_ctor_get(v_impl_1081_, 4);
lean_dec(v_unused_1154_);
v_unused_1155_ = lean_ctor_get(v_impl_1081_, 3);
lean_dec(v_unused_1155_);
v_unused_1156_ = lean_ctor_get(v_impl_1081_, 2);
lean_dec(v_unused_1156_);
v_unused_1157_ = lean_ctor_get(v_impl_1081_, 1);
lean_dec(v_unused_1157_);
v_unused_1158_ = lean_ctor_get(v_impl_1081_, 0);
lean_dec(v_unused_1158_);
v___x_1148_ = v_impl_1081_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_dec(v_impl_1081_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 4, v_r_1088_);
lean_ctor_set(v___x_1148_, 3, v___x_1146_);
lean_ctor_set(v___x_1148_, 2, v_v_1086_);
lean_ctor_set(v___x_1148_, 1, v_k_1085_);
lean_ctor_set(v___x_1148_, 0, v___x_1143_);
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_k_1085_);
lean_ctor_set(v_reuseFailAlloc_1152_, 2, v_v_1086_);
lean_ctor_set(v_reuseFailAlloc_1152_, 3, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1152_, 4, v_r_1088_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1166_; lean_object* v___x_1167_; lean_object* v___x_1169_; 
v_size_1166_ = lean_ctor_get(v_impl_1081_, 0);
v___x_1167_ = lean_nat_add(v___x_1082_, v_size_1166_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 3, v_impl_1081_);
lean_ctor_set(v___x_1078_, 0, v___x_1167_);
v___x_1169_ = v___x_1078_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_k_1073_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_v_1074_);
lean_ctor_set(v_reuseFailAlloc_1170_, 3, v_impl_1081_);
lean_ctor_set(v_reuseFailAlloc_1170_, 4, v_r_1076_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
else
{
if (lean_obj_tag(v_r_1076_) == 0)
{
lean_object* v_l_1171_; 
v_l_1171_ = lean_ctor_get(v_r_1076_, 3);
lean_inc(v_l_1171_);
if (lean_obj_tag(v_l_1171_) == 0)
{
lean_object* v_r_1172_; 
v_r_1172_ = lean_ctor_get(v_r_1076_, 4);
lean_inc(v_r_1172_);
if (lean_obj_tag(v_r_1172_) == 0)
{
lean_object* v_size_1173_; lean_object* v_k_1174_; lean_object* v_v_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1188_; 
v_size_1173_ = lean_ctor_get(v_r_1076_, 0);
v_k_1174_ = lean_ctor_get(v_r_1076_, 1);
v_v_1175_ = lean_ctor_get(v_r_1076_, 2);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_r_1076_);
if (v_isSharedCheck_1188_ == 0)
{
lean_object* v_unused_1189_; lean_object* v_unused_1190_; 
v_unused_1189_ = lean_ctor_get(v_r_1076_, 4);
lean_dec(v_unused_1189_);
v_unused_1190_ = lean_ctor_get(v_r_1076_, 3);
lean_dec(v_unused_1190_);
v___x_1177_ = v_r_1076_;
v_isShared_1178_ = v_isSharedCheck_1188_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_v_1175_);
lean_inc(v_k_1174_);
lean_inc(v_size_1173_);
lean_dec(v_r_1076_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1188_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v_size_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
v_size_1179_ = lean_ctor_get(v_l_1171_, 0);
v___x_1180_ = lean_nat_add(v___x_1082_, v_size_1173_);
lean_dec(v_size_1173_);
v___x_1181_ = lean_nat_add(v___x_1082_, v_size_1179_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 4, v_l_1171_);
lean_ctor_set(v___x_1177_, 3, v_impl_1081_);
lean_ctor_set(v___x_1177_, 2, v_v_1074_);
lean_ctor_set(v___x_1177_, 1, v_k_1073_);
lean_ctor_set(v___x_1177_, 0, v___x_1181_);
v___x_1183_ = v___x_1177_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1181_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_k_1073_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v_v_1074_);
lean_ctor_set(v_reuseFailAlloc_1187_, 3, v_impl_1081_);
lean_ctor_set(v_reuseFailAlloc_1187_, 4, v_l_1171_);
v___x_1183_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1185_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 4, v_r_1172_);
lean_ctor_set(v___x_1078_, 3, v___x_1183_);
lean_ctor_set(v___x_1078_, 2, v_v_1175_);
lean_ctor_set(v___x_1078_, 1, v_k_1174_);
lean_ctor_set(v___x_1078_, 0, v___x_1180_);
v___x_1185_ = v___x_1078_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_k_1174_);
lean_ctor_set(v_reuseFailAlloc_1186_, 2, v_v_1175_);
lean_ctor_set(v_reuseFailAlloc_1186_, 3, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1186_, 4, v_r_1172_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
else
{
lean_object* v_k_1191_; lean_object* v_v_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1215_; 
v_k_1191_ = lean_ctor_get(v_r_1076_, 1);
v_v_1192_ = lean_ctor_get(v_r_1076_, 2);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_r_1076_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; lean_object* v_unused_1217_; lean_object* v_unused_1218_; 
v_unused_1216_ = lean_ctor_get(v_r_1076_, 4);
lean_dec(v_unused_1216_);
v_unused_1217_ = lean_ctor_get(v_r_1076_, 3);
lean_dec(v_unused_1217_);
v_unused_1218_ = lean_ctor_get(v_r_1076_, 0);
lean_dec(v_unused_1218_);
v___x_1194_ = v_r_1076_;
v_isShared_1195_ = v_isSharedCheck_1215_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_v_1192_);
lean_inc(v_k_1191_);
lean_dec(v_r_1076_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1215_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v_k_1196_; lean_object* v_v_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1211_; 
v_k_1196_ = lean_ctor_get(v_l_1171_, 1);
v_v_1197_ = lean_ctor_get(v_l_1171_, 2);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_l_1171_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; lean_object* v_unused_1213_; lean_object* v_unused_1214_; 
v_unused_1212_ = lean_ctor_get(v_l_1171_, 4);
lean_dec(v_unused_1212_);
v_unused_1213_ = lean_ctor_get(v_l_1171_, 3);
lean_dec(v_unused_1213_);
v_unused_1214_ = lean_ctor_get(v_l_1171_, 0);
lean_dec(v_unused_1214_);
v___x_1199_ = v_l_1171_;
v_isShared_1200_ = v_isSharedCheck_1211_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_v_1197_);
lean_inc(v_k_1196_);
lean_dec(v_l_1171_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1211_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1201_ = lean_unsigned_to_nat(3u);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 4, v_r_1172_);
lean_ctor_set(v___x_1199_, 3, v_r_1172_);
lean_ctor_set(v___x_1199_, 2, v_v_1074_);
lean_ctor_set(v___x_1199_, 1, v_k_1073_);
lean_ctor_set(v___x_1199_, 0, v___x_1082_);
v___x_1203_ = v___x_1199_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v_k_1073_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v_v_1074_);
lean_ctor_set(v_reuseFailAlloc_1210_, 3, v_r_1172_);
lean_ctor_set(v_reuseFailAlloc_1210_, 4, v_r_1172_);
v___x_1203_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1205_; 
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 3, v_r_1172_);
lean_ctor_set(v___x_1194_, 0, v___x_1082_);
v___x_1205_ = v___x_1194_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_k_1191_);
lean_ctor_set(v_reuseFailAlloc_1209_, 2, v_v_1192_);
lean_ctor_set(v_reuseFailAlloc_1209_, 3, v_r_1172_);
lean_ctor_set(v_reuseFailAlloc_1209_, 4, v_r_1172_);
v___x_1205_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1207_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 4, v___x_1205_);
lean_ctor_set(v___x_1078_, 3, v___x_1203_);
lean_ctor_set(v___x_1078_, 2, v_v_1197_);
lean_ctor_set(v___x_1078_, 1, v_k_1196_);
lean_ctor_set(v___x_1078_, 0, v___x_1201_);
v___x_1207_ = v___x_1078_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_k_1196_);
lean_ctor_set(v_reuseFailAlloc_1208_, 2, v_v_1197_);
lean_ctor_set(v_reuseFailAlloc_1208_, 3, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1208_, 4, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1219_; 
v_r_1219_ = lean_ctor_get(v_r_1076_, 4);
lean_inc(v_r_1219_);
if (lean_obj_tag(v_r_1219_) == 0)
{
lean_object* v_k_1220_; lean_object* v_v_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1232_; 
v_k_1220_ = lean_ctor_get(v_r_1076_, 1);
v_v_1221_ = lean_ctor_get(v_r_1076_, 2);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_r_1076_);
if (v_isSharedCheck_1232_ == 0)
{
lean_object* v_unused_1233_; lean_object* v_unused_1234_; lean_object* v_unused_1235_; 
v_unused_1233_ = lean_ctor_get(v_r_1076_, 4);
lean_dec(v_unused_1233_);
v_unused_1234_ = lean_ctor_get(v_r_1076_, 3);
lean_dec(v_unused_1234_);
v_unused_1235_ = lean_ctor_get(v_r_1076_, 0);
lean_dec(v_unused_1235_);
v___x_1223_ = v_r_1076_;
v_isShared_1224_ = v_isSharedCheck_1232_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_v_1221_);
lean_inc(v_k_1220_);
lean_dec(v_r_1076_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1232_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v___x_1227_; 
v___x_1225_ = lean_unsigned_to_nat(3u);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 4, v_l_1171_);
lean_ctor_set(v___x_1223_, 2, v_v_1074_);
lean_ctor_set(v___x_1223_, 1, v_k_1073_);
lean_ctor_set(v___x_1223_, 0, v___x_1082_);
v___x_1227_ = v___x_1223_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_k_1073_);
lean_ctor_set(v_reuseFailAlloc_1231_, 2, v_v_1074_);
lean_ctor_set(v_reuseFailAlloc_1231_, 3, v_l_1171_);
lean_ctor_set(v_reuseFailAlloc_1231_, 4, v_l_1171_);
v___x_1227_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1229_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 4, v_r_1219_);
lean_ctor_set(v___x_1078_, 3, v___x_1227_);
lean_ctor_set(v___x_1078_, 2, v_v_1221_);
lean_ctor_set(v___x_1078_, 1, v_k_1220_);
lean_ctor_set(v___x_1078_, 0, v___x_1225_);
v___x_1229_ = v___x_1078_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_k_1220_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_v_1221_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1230_, 4, v_r_1219_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
else
{
lean_object* v_size_1236_; lean_object* v_k_1237_; lean_object* v_v_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1249_; 
v_size_1236_ = lean_ctor_get(v_r_1076_, 0);
v_k_1237_ = lean_ctor_get(v_r_1076_, 1);
v_v_1238_ = lean_ctor_get(v_r_1076_, 2);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_r_1076_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; lean_object* v_unused_1251_; 
v_unused_1250_ = lean_ctor_get(v_r_1076_, 4);
lean_dec(v_unused_1250_);
v_unused_1251_ = lean_ctor_get(v_r_1076_, 3);
lean_dec(v_unused_1251_);
v___x_1240_ = v_r_1076_;
v_isShared_1241_ = v_isSharedCheck_1249_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_v_1238_);
lean_inc(v_k_1237_);
lean_inc(v_size_1236_);
lean_dec(v_r_1076_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1249_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 3, v_r_1219_);
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_size_1236_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_k_1237_);
lean_ctor_set(v_reuseFailAlloc_1248_, 2, v_v_1238_);
lean_ctor_set(v_reuseFailAlloc_1248_, 3, v_r_1219_);
lean_ctor_set(v_reuseFailAlloc_1248_, 4, v_r_1219_);
v___x_1243_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1246_; 
v___x_1244_ = lean_unsigned_to_nat(2u);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 4, v___x_1243_);
lean_ctor_set(v___x_1078_, 3, v_r_1219_);
lean_ctor_set(v___x_1078_, 0, v___x_1244_);
v___x_1246_ = v___x_1078_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v_k_1073_);
lean_ctor_set(v_reuseFailAlloc_1247_, 2, v_v_1074_);
lean_ctor_set(v_reuseFailAlloc_1247_, 3, v_r_1219_);
lean_ctor_set(v_reuseFailAlloc_1247_, 4, v___x_1243_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
}
else
{
lean_object* v___x_1253_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 3, v_r_1076_);
lean_ctor_set(v___x_1078_, 0, v___x_1082_);
v___x_1253_ = v___x_1078_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_k_1073_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v_v_1074_);
lean_ctor_set(v_reuseFailAlloc_1254_, 3, v_r_1076_);
lean_ctor_set(v_reuseFailAlloc_1254_, 4, v_r_1076_);
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
case 1:
{
lean_del_object(v___x_1078_);
lean_dec(v_v_1074_);
lean_dec(v_k_1073_);
if (lean_obj_tag(v_l_1075_) == 0)
{
if (lean_obj_tag(v_r_1076_) == 0)
{
lean_object* v_size_1255_; lean_object* v_k_1256_; lean_object* v_v_1257_; lean_object* v_l_1258_; lean_object* v_r_1259_; lean_object* v_size_1260_; lean_object* v_k_1261_; lean_object* v_v_1262_; lean_object* v_l_1263_; lean_object* v_r_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v_size_1255_ = lean_ctor_get(v_l_1075_, 0);
v_k_1256_ = lean_ctor_get(v_l_1075_, 1);
v_v_1257_ = lean_ctor_get(v_l_1075_, 2);
v_l_1258_ = lean_ctor_get(v_l_1075_, 3);
v_r_1259_ = lean_ctor_get(v_l_1075_, 4);
lean_inc(v_r_1259_);
v_size_1260_ = lean_ctor_get(v_r_1076_, 0);
v_k_1261_ = lean_ctor_get(v_r_1076_, 1);
v_v_1262_ = lean_ctor_get(v_r_1076_, 2);
v_l_1263_ = lean_ctor_get(v_r_1076_, 3);
lean_inc(v_l_1263_);
v_r_1264_ = lean_ctor_get(v_r_1076_, 4);
v___x_1265_ = lean_unsigned_to_nat(1u);
v___x_1266_ = lean_nat_dec_lt(v_size_1255_, v_size_1260_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1402_; 
lean_inc(v_l_1258_);
lean_inc(v_v_1257_);
lean_inc(v_k_1256_);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_l_1075_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; lean_object* v_unused_1404_; lean_object* v_unused_1405_; lean_object* v_unused_1406_; lean_object* v_unused_1407_; 
v_unused_1403_ = lean_ctor_get(v_l_1075_, 4);
lean_dec(v_unused_1403_);
v_unused_1404_ = lean_ctor_get(v_l_1075_, 3);
lean_dec(v_unused_1404_);
v_unused_1405_ = lean_ctor_get(v_l_1075_, 2);
lean_dec(v_unused_1405_);
v_unused_1406_ = lean_ctor_get(v_l_1075_, 1);
lean_dec(v_unused_1406_);
v_unused_1407_ = lean_ctor_get(v_l_1075_, 0);
lean_dec(v_unused_1407_);
v___x_1268_ = v_l_1075_;
v_isShared_1269_ = v_isSharedCheck_1402_;
goto v_resetjp_1267_;
}
else
{
lean_dec(v_l_1075_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1402_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v_tree_1271_; 
v___x_1270_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1256_, v_v_1257_, v_l_1258_, v_r_1259_);
v_tree_1271_ = lean_ctor_get(v___x_1270_, 2);
if (lean_obj_tag(v_tree_1271_) == 0)
{
lean_object* v_k_1272_; lean_object* v_v_1273_; lean_object* v_size_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
lean_inc_ref(v_tree_1271_);
v_k_1272_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_k_1272_);
v_v_1273_ = lean_ctor_get(v___x_1270_, 1);
lean_inc(v_v_1273_);
lean_dec_ref(v___x_1270_);
v_size_1274_ = lean_ctor_get(v_tree_1271_, 0);
v___x_1275_ = lean_unsigned_to_nat(3u);
v___x_1276_ = lean_nat_mul(v___x_1275_, v_size_1274_);
v___x_1277_ = lean_nat_dec_lt(v___x_1276_, v_size_1260_);
lean_dec(v___x_1276_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
lean_dec(v_l_1263_);
v___x_1278_ = lean_nat_add(v___x_1265_, v_size_1274_);
v___x_1279_ = lean_nat_add(v___x_1278_, v_size_1260_);
lean_dec(v___x_1278_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 4, v_r_1076_);
lean_ctor_set(v___x_1268_, 3, v_tree_1271_);
lean_ctor_set(v___x_1268_, 2, v_v_1273_);
lean_ctor_set(v___x_1268_, 1, v_k_1272_);
lean_ctor_set(v___x_1268_, 0, v___x_1279_);
v___x_1281_ = v___x_1268_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_k_1272_);
lean_ctor_set(v_reuseFailAlloc_1282_, 2, v_v_1273_);
lean_ctor_set(v_reuseFailAlloc_1282_, 3, v_tree_1271_);
lean_ctor_set(v_reuseFailAlloc_1282_, 4, v_r_1076_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
else
{
lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1337_; 
lean_inc(v_r_1264_);
lean_inc(v_v_1262_);
lean_inc(v_k_1261_);
lean_inc(v_size_1260_);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_r_1076_);
if (v_isSharedCheck_1337_ == 0)
{
lean_object* v_unused_1338_; lean_object* v_unused_1339_; lean_object* v_unused_1340_; lean_object* v_unused_1341_; lean_object* v_unused_1342_; 
v_unused_1338_ = lean_ctor_get(v_r_1076_, 4);
lean_dec(v_unused_1338_);
v_unused_1339_ = lean_ctor_get(v_r_1076_, 3);
lean_dec(v_unused_1339_);
v_unused_1340_ = lean_ctor_get(v_r_1076_, 2);
lean_dec(v_unused_1340_);
v_unused_1341_ = lean_ctor_get(v_r_1076_, 1);
lean_dec(v_unused_1341_);
v_unused_1342_ = lean_ctor_get(v_r_1076_, 0);
lean_dec(v_unused_1342_);
v___x_1284_ = v_r_1076_;
v_isShared_1285_ = v_isSharedCheck_1337_;
goto v_resetjp_1283_;
}
else
{
lean_dec(v_r_1076_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1337_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v_size_1286_; lean_object* v_k_1287_; lean_object* v_v_1288_; lean_object* v_l_1289_; lean_object* v_r_1290_; lean_object* v_size_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v_size_1286_ = lean_ctor_get(v_l_1263_, 0);
v_k_1287_ = lean_ctor_get(v_l_1263_, 1);
v_v_1288_ = lean_ctor_get(v_l_1263_, 2);
v_l_1289_ = lean_ctor_get(v_l_1263_, 3);
v_r_1290_ = lean_ctor_get(v_l_1263_, 4);
v_size_1291_ = lean_ctor_get(v_r_1264_, 0);
v___x_1292_ = lean_unsigned_to_nat(2u);
v___x_1293_ = lean_nat_mul(v___x_1292_, v_size_1291_);
v___x_1294_ = lean_nat_dec_lt(v_size_1286_, v___x_1293_);
lean_dec(v___x_1293_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1322_; 
lean_inc(v_r_1290_);
lean_inc(v_l_1289_);
lean_inc(v_v_1288_);
lean_inc(v_k_1287_);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_l_1263_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; lean_object* v_unused_1324_; lean_object* v_unused_1325_; lean_object* v_unused_1326_; lean_object* v_unused_1327_; 
v_unused_1323_ = lean_ctor_get(v_l_1263_, 4);
lean_dec(v_unused_1323_);
v_unused_1324_ = lean_ctor_get(v_l_1263_, 3);
lean_dec(v_unused_1324_);
v_unused_1325_ = lean_ctor_get(v_l_1263_, 2);
lean_dec(v_unused_1325_);
v_unused_1326_ = lean_ctor_get(v_l_1263_, 1);
lean_dec(v_unused_1326_);
v_unused_1327_ = lean_ctor_get(v_l_1263_, 0);
lean_dec(v_unused_1327_);
v___x_1296_ = v_l_1263_;
v_isShared_1297_ = v_isSharedCheck_1322_;
goto v_resetjp_1295_;
}
else
{
lean_dec(v_l_1263_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1322_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1312_; 
v___x_1298_ = lean_nat_add(v___x_1265_, v_size_1274_);
v___x_1299_ = lean_nat_add(v___x_1298_, v_size_1260_);
lean_dec(v_size_1260_);
if (lean_obj_tag(v_l_1289_) == 0)
{
lean_object* v_size_1320_; 
v_size_1320_ = lean_ctor_get(v_l_1289_, 0);
lean_inc(v_size_1320_);
v___y_1312_ = v_size_1320_;
goto v___jp_1311_;
}
else
{
lean_object* v___x_1321_; 
v___x_1321_ = lean_unsigned_to_nat(0u);
v___y_1312_ = v___x_1321_;
goto v___jp_1311_;
}
v___jp_1300_:
{
lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1304_ = lean_nat_add(v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec(v___y_1302_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 4, v_r_1264_);
lean_ctor_set(v___x_1296_, 3, v_r_1290_);
lean_ctor_set(v___x_1296_, 2, v_v_1262_);
lean_ctor_set(v___x_1296_, 1, v_k_1261_);
lean_ctor_set(v___x_1296_, 0, v___x_1304_);
v___x_1306_ = v___x_1296_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1304_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_k_1261_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v_v_1262_);
lean_ctor_set(v_reuseFailAlloc_1310_, 3, v_r_1290_);
lean_ctor_set(v_reuseFailAlloc_1310_, 4, v_r_1264_);
v___x_1306_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1308_; 
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 4, v___x_1306_);
lean_ctor_set(v___x_1284_, 3, v___y_1301_);
lean_ctor_set(v___x_1284_, 2, v_v_1288_);
lean_ctor_set(v___x_1284_, 1, v_k_1287_);
lean_ctor_set(v___x_1284_, 0, v___x_1299_);
v___x_1308_ = v___x_1284_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1299_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v_k_1287_);
lean_ctor_set(v_reuseFailAlloc_1309_, 2, v_v_1288_);
lean_ctor_set(v_reuseFailAlloc_1309_, 3, v___y_1301_);
lean_ctor_set(v_reuseFailAlloc_1309_, 4, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
v___jp_1311_:
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1313_ = lean_nat_add(v___x_1298_, v___y_1312_);
lean_dec(v___y_1312_);
lean_dec(v___x_1298_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 4, v_l_1289_);
lean_ctor_set(v___x_1268_, 3, v_tree_1271_);
lean_ctor_set(v___x_1268_, 2, v_v_1273_);
lean_ctor_set(v___x_1268_, 1, v_k_1272_);
lean_ctor_set(v___x_1268_, 0, v___x_1313_);
v___x_1315_ = v___x_1268_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_k_1272_);
lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_v_1273_);
lean_ctor_set(v_reuseFailAlloc_1319_, 3, v_tree_1271_);
lean_ctor_set(v_reuseFailAlloc_1319_, 4, v_l_1289_);
v___x_1315_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1316_; 
v___x_1316_ = lean_nat_add(v___x_1265_, v_size_1291_);
if (lean_obj_tag(v_r_1290_) == 0)
{
lean_object* v_size_1317_; 
v_size_1317_ = lean_ctor_get(v_r_1290_, 0);
lean_inc(v_size_1317_);
v___y_1301_ = v___x_1315_;
v___y_1302_ = v___x_1316_;
v___y_1303_ = v_size_1317_;
goto v___jp_1300_;
}
else
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_unsigned_to_nat(0u);
v___y_1301_ = v___x_1315_;
v___y_1302_ = v___x_1316_;
v___y_1303_ = v___x_1318_;
goto v___jp_1300_;
}
}
}
}
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1328_ = lean_nat_add(v___x_1265_, v_size_1274_);
v___x_1329_ = lean_nat_add(v___x_1328_, v_size_1260_);
lean_dec(v_size_1260_);
v___x_1330_ = lean_nat_add(v___x_1328_, v_size_1286_);
lean_dec(v___x_1328_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 4, v_l_1263_);
lean_ctor_set(v___x_1284_, 3, v_tree_1271_);
lean_ctor_set(v___x_1284_, 2, v_v_1273_);
lean_ctor_set(v___x_1284_, 1, v_k_1272_);
lean_ctor_set(v___x_1284_, 0, v___x_1330_);
v___x_1332_ = v___x_1284_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1330_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_k_1272_);
lean_ctor_set(v_reuseFailAlloc_1336_, 2, v_v_1273_);
lean_ctor_set(v_reuseFailAlloc_1336_, 3, v_tree_1271_);
lean_ctor_set(v_reuseFailAlloc_1336_, 4, v_l_1263_);
v___x_1332_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
lean_object* v___x_1334_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 4, v_r_1264_);
lean_ctor_set(v___x_1268_, 3, v___x_1332_);
lean_ctor_set(v___x_1268_, 2, v_v_1262_);
lean_ctor_set(v___x_1268_, 1, v_k_1261_);
lean_ctor_set(v___x_1268_, 0, v___x_1329_);
v___x_1334_ = v___x_1268_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_k_1261_);
lean_ctor_set(v_reuseFailAlloc_1335_, 2, v_v_1262_);
lean_ctor_set(v_reuseFailAlloc_1335_, 3, v___x_1332_);
lean_ctor_set(v_reuseFailAlloc_1335_, 4, v_r_1264_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
}
else
{
lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1396_; 
lean_inc(v_r_1264_);
lean_inc(v_v_1262_);
lean_inc(v_k_1261_);
lean_inc(v_size_1260_);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_r_1076_);
if (v_isSharedCheck_1396_ == 0)
{
lean_object* v_unused_1397_; lean_object* v_unused_1398_; lean_object* v_unused_1399_; lean_object* v_unused_1400_; lean_object* v_unused_1401_; 
v_unused_1397_ = lean_ctor_get(v_r_1076_, 4);
lean_dec(v_unused_1397_);
v_unused_1398_ = lean_ctor_get(v_r_1076_, 3);
lean_dec(v_unused_1398_);
v_unused_1399_ = lean_ctor_get(v_r_1076_, 2);
lean_dec(v_unused_1399_);
v_unused_1400_ = lean_ctor_get(v_r_1076_, 1);
lean_dec(v_unused_1400_);
v_unused_1401_ = lean_ctor_get(v_r_1076_, 0);
lean_dec(v_unused_1401_);
v___x_1344_ = v_r_1076_;
v_isShared_1345_ = v_isSharedCheck_1396_;
goto v_resetjp_1343_;
}
else
{
lean_dec(v_r_1076_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1396_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
if (lean_obj_tag(v_l_1263_) == 0)
{
if (lean_obj_tag(v_r_1264_) == 0)
{
lean_object* v_k_1346_; lean_object* v_v_1347_; lean_object* v_size_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1352_; 
lean_inc(v_tree_1271_);
v_k_1346_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_k_1346_);
v_v_1347_ = lean_ctor_get(v___x_1270_, 1);
lean_inc(v_v_1347_);
lean_dec_ref(v___x_1270_);
v_size_1348_ = lean_ctor_get(v_l_1263_, 0);
v___x_1349_ = lean_nat_add(v___x_1265_, v_size_1260_);
lean_dec(v_size_1260_);
v___x_1350_ = lean_nat_add(v___x_1265_, v_size_1348_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 4, v_l_1263_);
lean_ctor_set(v___x_1344_, 3, v_tree_1271_);
lean_ctor_set(v___x_1344_, 2, v_v_1347_);
lean_ctor_set(v___x_1344_, 1, v_k_1346_);
lean_ctor_set(v___x_1344_, 0, v___x_1350_);
v___x_1352_ = v___x_1344_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_k_1346_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_v_1347_);
lean_ctor_set(v_reuseFailAlloc_1356_, 3, v_tree_1271_);
lean_ctor_set(v_reuseFailAlloc_1356_, 4, v_l_1263_);
v___x_1352_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1354_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 4, v_r_1264_);
lean_ctor_set(v___x_1268_, 3, v___x_1352_);
lean_ctor_set(v___x_1268_, 2, v_v_1262_);
lean_ctor_set(v___x_1268_, 1, v_k_1261_);
lean_ctor_set(v___x_1268_, 0, v___x_1349_);
v___x_1354_ = v___x_1268_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_k_1261_);
lean_ctor_set(v_reuseFailAlloc_1355_, 2, v_v_1262_);
lean_ctor_set(v_reuseFailAlloc_1355_, 3, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1355_, 4, v_r_1264_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
else
{
lean_object* v_k_1357_; lean_object* v_v_1358_; lean_object* v_k_1359_; lean_object* v_v_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1374_; 
lean_dec(v_size_1260_);
v_k_1357_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_k_1357_);
v_v_1358_ = lean_ctor_get(v___x_1270_, 1);
lean_inc(v_v_1358_);
lean_dec_ref(v___x_1270_);
v_k_1359_ = lean_ctor_get(v_l_1263_, 1);
v_v_1360_ = lean_ctor_get(v_l_1263_, 2);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_l_1263_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; lean_object* v_unused_1376_; lean_object* v_unused_1377_; 
v_unused_1375_ = lean_ctor_get(v_l_1263_, 4);
lean_dec(v_unused_1375_);
v_unused_1376_ = lean_ctor_get(v_l_1263_, 3);
lean_dec(v_unused_1376_);
v_unused_1377_ = lean_ctor_get(v_l_1263_, 0);
lean_dec(v_unused_1377_);
v___x_1362_ = v_l_1263_;
v_isShared_1363_ = v_isSharedCheck_1374_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_v_1360_);
lean_inc(v_k_1359_);
lean_dec(v_l_1263_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1374_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1364_ = lean_unsigned_to_nat(3u);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 4, v_r_1264_);
lean_ctor_set(v___x_1362_, 3, v_r_1264_);
lean_ctor_set(v___x_1362_, 2, v_v_1358_);
lean_ctor_set(v___x_1362_, 1, v_k_1357_);
lean_ctor_set(v___x_1362_, 0, v___x_1265_);
v___x_1366_ = v___x_1362_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_k_1357_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_v_1358_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_r_1264_);
lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_r_1264_);
v___x_1366_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1368_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 3, v_r_1264_);
lean_ctor_set(v___x_1344_, 0, v___x_1265_);
v___x_1368_ = v___x_1344_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_k_1261_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v_v_1262_);
lean_ctor_set(v_reuseFailAlloc_1372_, 3, v_r_1264_);
lean_ctor_set(v_reuseFailAlloc_1372_, 4, v_r_1264_);
v___x_1368_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1370_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 4, v___x_1368_);
lean_ctor_set(v___x_1268_, 3, v___x_1366_);
lean_ctor_set(v___x_1268_, 2, v_v_1360_);
lean_ctor_set(v___x_1268_, 1, v_k_1359_);
lean_ctor_set(v___x_1268_, 0, v___x_1364_);
v___x_1370_ = v___x_1268_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_k_1359_);
lean_ctor_set(v_reuseFailAlloc_1371_, 2, v_v_1360_);
lean_ctor_set(v_reuseFailAlloc_1371_, 3, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1371_, 4, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1264_) == 0)
{
lean_object* v_k_1378_; lean_object* v_v_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
lean_dec(v_size_1260_);
v_k_1378_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_k_1378_);
v_v_1379_ = lean_ctor_get(v___x_1270_, 1);
lean_inc(v_v_1379_);
lean_dec_ref(v___x_1270_);
v___x_1380_ = lean_unsigned_to_nat(3u);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 4, v_l_1263_);
lean_ctor_set(v___x_1344_, 2, v_v_1379_);
lean_ctor_set(v___x_1344_, 1, v_k_1378_);
lean_ctor_set(v___x_1344_, 0, v___x_1265_);
v___x_1382_ = v___x_1344_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_k_1378_);
lean_ctor_set(v_reuseFailAlloc_1386_, 2, v_v_1379_);
lean_ctor_set(v_reuseFailAlloc_1386_, 3, v_l_1263_);
lean_ctor_set(v_reuseFailAlloc_1386_, 4, v_l_1263_);
v___x_1382_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
lean_object* v___x_1384_; 
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 4, v_r_1264_);
lean_ctor_set(v___x_1268_, 3, v___x_1382_);
lean_ctor_set(v___x_1268_, 2, v_v_1262_);
lean_ctor_set(v___x_1268_, 1, v_k_1261_);
lean_ctor_set(v___x_1268_, 0, v___x_1380_);
v___x_1384_ = v___x_1268_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_k_1261_);
lean_ctor_set(v_reuseFailAlloc_1385_, 2, v_v_1262_);
lean_ctor_set(v_reuseFailAlloc_1385_, 3, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1385_, 4, v_r_1264_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
else
{
lean_object* v_k_1387_; lean_object* v_v_1388_; lean_object* v___x_1390_; 
v_k_1387_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_k_1387_);
v_v_1388_ = lean_ctor_get(v___x_1270_, 1);
lean_inc(v_v_1388_);
lean_dec_ref(v___x_1270_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 3, v_r_1264_);
v___x_1390_ = v___x_1344_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_size_1260_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_k_1261_);
lean_ctor_set(v_reuseFailAlloc_1395_, 2, v_v_1262_);
lean_ctor_set(v_reuseFailAlloc_1395_, 3, v_r_1264_);
lean_ctor_set(v_reuseFailAlloc_1395_, 4, v_r_1264_);
v___x_1390_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1391_ = lean_unsigned_to_nat(2u);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 4, v___x_1390_);
lean_ctor_set(v___x_1268_, 3, v_r_1264_);
lean_ctor_set(v___x_1268_, 2, v_v_1388_);
lean_ctor_set(v___x_1268_, 1, v_k_1387_);
lean_ctor_set(v___x_1268_, 0, v___x_1391_);
v___x_1393_ = v___x_1268_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_k_1387_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v_v_1388_);
lean_ctor_set(v_reuseFailAlloc_1394_, 3, v_r_1264_);
lean_ctor_set(v_reuseFailAlloc_1394_, 4, v___x_1390_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
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
lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1560_; 
lean_inc(v_r_1264_);
lean_inc(v_v_1262_);
lean_inc(v_k_1261_);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_r_1076_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; lean_object* v_unused_1562_; lean_object* v_unused_1563_; lean_object* v_unused_1564_; lean_object* v_unused_1565_; 
v_unused_1561_ = lean_ctor_get(v_r_1076_, 4);
lean_dec(v_unused_1561_);
v_unused_1562_ = lean_ctor_get(v_r_1076_, 3);
lean_dec(v_unused_1562_);
v_unused_1563_ = lean_ctor_get(v_r_1076_, 2);
lean_dec(v_unused_1563_);
v_unused_1564_ = lean_ctor_get(v_r_1076_, 1);
lean_dec(v_unused_1564_);
v_unused_1565_ = lean_ctor_get(v_r_1076_, 0);
lean_dec(v_unused_1565_);
v___x_1409_ = v_r_1076_;
v_isShared_1410_ = v_isSharedCheck_1560_;
goto v_resetjp_1408_;
}
else
{
lean_dec(v_r_1076_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1560_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v_tree_1412_; 
v___x_1411_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1261_, v_v_1262_, v_l_1263_, v_r_1264_);
v_tree_1412_ = lean_ctor_get(v___x_1411_, 2);
lean_inc(v_tree_1412_);
if (lean_obj_tag(v_tree_1412_) == 0)
{
lean_object* v_k_1413_; lean_object* v_v_1414_; lean_object* v_size_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v_k_1413_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_k_1413_);
v_v_1414_ = lean_ctor_get(v___x_1411_, 1);
lean_inc(v_v_1414_);
lean_dec_ref(v___x_1411_);
v_size_1415_ = lean_ctor_get(v_tree_1412_, 0);
v___x_1416_ = lean_unsigned_to_nat(3u);
v___x_1417_ = lean_nat_mul(v___x_1416_, v_size_1415_);
v___x_1418_ = lean_nat_dec_lt(v___x_1417_, v_size_1255_);
lean_dec(v___x_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; 
lean_dec(v_r_1259_);
v___x_1419_ = lean_nat_add(v___x_1265_, v_size_1255_);
v___x_1420_ = lean_nat_add(v___x_1419_, v_size_1415_);
lean_dec(v___x_1419_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v_tree_1412_);
lean_ctor_set(v___x_1409_, 3, v_l_1075_);
lean_ctor_set(v___x_1409_, 2, v_v_1414_);
lean_ctor_set(v___x_1409_, 1, v_k_1413_);
lean_ctor_set(v___x_1409_, 0, v___x_1420_);
v___x_1422_ = v___x_1409_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_k_1413_);
lean_ctor_set(v_reuseFailAlloc_1423_, 2, v_v_1414_);
lean_ctor_set(v_reuseFailAlloc_1423_, 3, v_l_1075_);
lean_ctor_set(v_reuseFailAlloc_1423_, 4, v_tree_1412_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
else
{
lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1489_; 
lean_inc(v_l_1258_);
lean_inc(v_v_1257_);
lean_inc(v_k_1256_);
lean_inc(v_size_1255_);
v_isSharedCheck_1489_ = !lean_is_exclusive(v_l_1075_);
if (v_isSharedCheck_1489_ == 0)
{
lean_object* v_unused_1490_; lean_object* v_unused_1491_; lean_object* v_unused_1492_; lean_object* v_unused_1493_; lean_object* v_unused_1494_; 
v_unused_1490_ = lean_ctor_get(v_l_1075_, 4);
lean_dec(v_unused_1490_);
v_unused_1491_ = lean_ctor_get(v_l_1075_, 3);
lean_dec(v_unused_1491_);
v_unused_1492_ = lean_ctor_get(v_l_1075_, 2);
lean_dec(v_unused_1492_);
v_unused_1493_ = lean_ctor_get(v_l_1075_, 1);
lean_dec(v_unused_1493_);
v_unused_1494_ = lean_ctor_get(v_l_1075_, 0);
lean_dec(v_unused_1494_);
v___x_1425_ = v_l_1075_;
v_isShared_1426_ = v_isSharedCheck_1489_;
goto v_resetjp_1424_;
}
else
{
lean_dec(v_l_1075_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1489_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v_size_1427_; lean_object* v_size_1428_; lean_object* v_k_1429_; lean_object* v_v_1430_; lean_object* v_l_1431_; lean_object* v_r_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; uint8_t v___x_1435_; 
v_size_1427_ = lean_ctor_get(v_l_1258_, 0);
v_size_1428_ = lean_ctor_get(v_r_1259_, 0);
v_k_1429_ = lean_ctor_get(v_r_1259_, 1);
v_v_1430_ = lean_ctor_get(v_r_1259_, 2);
v_l_1431_ = lean_ctor_get(v_r_1259_, 3);
v_r_1432_ = lean_ctor_get(v_r_1259_, 4);
v___x_1433_ = lean_unsigned_to_nat(2u);
v___x_1434_ = lean_nat_mul(v___x_1433_, v_size_1427_);
v___x_1435_ = lean_nat_dec_lt(v_size_1428_, v___x_1434_);
lean_dec(v___x_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1473_; 
lean_inc(v_r_1432_);
lean_inc(v_l_1431_);
lean_inc(v_v_1430_);
lean_inc(v_k_1429_);
lean_del_object(v___x_1425_);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_r_1259_);
if (v_isSharedCheck_1473_ == 0)
{
lean_object* v_unused_1474_; lean_object* v_unused_1475_; lean_object* v_unused_1476_; lean_object* v_unused_1477_; lean_object* v_unused_1478_; 
v_unused_1474_ = lean_ctor_get(v_r_1259_, 4);
lean_dec(v_unused_1474_);
v_unused_1475_ = lean_ctor_get(v_r_1259_, 3);
lean_dec(v_unused_1475_);
v_unused_1476_ = lean_ctor_get(v_r_1259_, 2);
lean_dec(v_unused_1476_);
v_unused_1477_ = lean_ctor_get(v_r_1259_, 1);
lean_dec(v_unused_1477_);
v_unused_1478_ = lean_ctor_get(v_r_1259_, 0);
lean_dec(v_unused_1478_);
v___x_1437_ = v_r_1259_;
v_isShared_1438_ = v_isSharedCheck_1473_;
goto v_resetjp_1436_;
}
else
{
lean_dec(v_r_1259_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1473_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___x_1461_; lean_object* v___y_1463_; 
v___x_1439_ = lean_nat_add(v___x_1265_, v_size_1255_);
lean_dec(v_size_1255_);
v___x_1440_ = lean_nat_add(v___x_1439_, v_size_1415_);
lean_dec(v___x_1439_);
v___x_1461_ = lean_nat_add(v___x_1265_, v_size_1427_);
if (lean_obj_tag(v_l_1431_) == 0)
{
lean_object* v_size_1471_; 
v_size_1471_ = lean_ctor_get(v_l_1431_, 0);
lean_inc(v_size_1471_);
v___y_1463_ = v_size_1471_;
goto v___jp_1462_;
}
else
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_unsigned_to_nat(0u);
v___y_1463_ = v___x_1472_;
goto v___jp_1462_;
}
v___jp_1441_:
{
lean_object* v___x_1445_; lean_object* v___x_1447_; 
v___x_1445_ = lean_nat_add(v___y_1442_, v___y_1444_);
lean_dec(v___y_1444_);
lean_dec(v___y_1442_);
lean_inc_ref(v_tree_1412_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 4, v_tree_1412_);
lean_ctor_set(v___x_1437_, 3, v_r_1432_);
lean_ctor_set(v___x_1437_, 2, v_v_1414_);
lean_ctor_set(v___x_1437_, 1, v_k_1413_);
lean_ctor_set(v___x_1437_, 0, v___x_1445_);
v___x_1447_ = v___x_1437_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_k_1413_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v_v_1414_);
lean_ctor_set(v_reuseFailAlloc_1460_, 3, v_r_1432_);
lean_ctor_set(v_reuseFailAlloc_1460_, 4, v_tree_1412_);
v___x_1447_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
v_isSharedCheck_1454_ = !lean_is_exclusive(v_tree_1412_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; lean_object* v_unused_1456_; lean_object* v_unused_1457_; lean_object* v_unused_1458_; lean_object* v_unused_1459_; 
v_unused_1455_ = lean_ctor_get(v_tree_1412_, 4);
lean_dec(v_unused_1455_);
v_unused_1456_ = lean_ctor_get(v_tree_1412_, 3);
lean_dec(v_unused_1456_);
v_unused_1457_ = lean_ctor_get(v_tree_1412_, 2);
lean_dec(v_unused_1457_);
v_unused_1458_ = lean_ctor_get(v_tree_1412_, 1);
lean_dec(v_unused_1458_);
v_unused_1459_ = lean_ctor_get(v_tree_1412_, 0);
lean_dec(v_unused_1459_);
v___x_1449_ = v_tree_1412_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_dec(v_tree_1412_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 4, v___x_1447_);
lean_ctor_set(v___x_1449_, 3, v___y_1443_);
lean_ctor_set(v___x_1449_, 2, v_v_1430_);
lean_ctor_set(v___x_1449_, 1, v_k_1429_);
lean_ctor_set(v___x_1449_, 0, v___x_1440_);
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_k_1429_);
lean_ctor_set(v_reuseFailAlloc_1453_, 2, v_v_1430_);
lean_ctor_set(v_reuseFailAlloc_1453_, 3, v___y_1443_);
lean_ctor_set(v_reuseFailAlloc_1453_, 4, v___x_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
v___jp_1462_:
{
lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1464_ = lean_nat_add(v___x_1461_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec(v___x_1461_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v_l_1431_);
lean_ctor_set(v___x_1409_, 3, v_l_1258_);
lean_ctor_set(v___x_1409_, 2, v_v_1257_);
lean_ctor_set(v___x_1409_, 1, v_k_1256_);
lean_ctor_set(v___x_1409_, 0, v___x_1464_);
v___x_1466_ = v___x_1409_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1464_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1470_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1470_, 3, v_l_1258_);
lean_ctor_set(v_reuseFailAlloc_1470_, 4, v_l_1431_);
v___x_1466_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1467_; 
v___x_1467_ = lean_nat_add(v___x_1265_, v_size_1415_);
if (lean_obj_tag(v_r_1432_) == 0)
{
lean_object* v_size_1468_; 
v_size_1468_ = lean_ctor_get(v_r_1432_, 0);
lean_inc(v_size_1468_);
v___y_1442_ = v___x_1467_;
v___y_1443_ = v___x_1466_;
v___y_1444_ = v_size_1468_;
goto v___jp_1441_;
}
else
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_unsigned_to_nat(0u);
v___y_1442_ = v___x_1467_;
v___y_1443_ = v___x_1466_;
v___y_1444_ = v___x_1469_;
goto v___jp_1441_;
}
}
}
}
}
else
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1479_ = lean_nat_add(v___x_1265_, v_size_1255_);
lean_dec(v_size_1255_);
v___x_1480_ = lean_nat_add(v___x_1479_, v_size_1415_);
lean_dec(v___x_1479_);
v___x_1481_ = lean_nat_add(v___x_1265_, v_size_1415_);
v___x_1482_ = lean_nat_add(v___x_1481_, v_size_1428_);
lean_dec(v___x_1481_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v_tree_1412_);
lean_ctor_set(v___x_1409_, 3, v_r_1259_);
lean_ctor_set(v___x_1409_, 2, v_v_1414_);
lean_ctor_set(v___x_1409_, 1, v_k_1413_);
lean_ctor_set(v___x_1409_, 0, v___x_1482_);
v___x_1484_ = v___x_1409_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v_k_1413_);
lean_ctor_set(v_reuseFailAlloc_1488_, 2, v_v_1414_);
lean_ctor_set(v_reuseFailAlloc_1488_, 3, v_r_1259_);
lean_ctor_set(v_reuseFailAlloc_1488_, 4, v_tree_1412_);
v___x_1484_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1486_; 
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 4, v___x_1484_);
lean_ctor_set(v___x_1425_, 0, v___x_1480_);
v___x_1486_ = v___x_1425_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1487_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1487_, 3, v_l_1258_);
lean_ctor_set(v_reuseFailAlloc_1487_, 4, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1258_) == 0)
{
lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1518_; 
lean_inc_ref(v_l_1258_);
lean_inc(v_v_1257_);
lean_inc(v_k_1256_);
lean_inc(v_size_1255_);
v_isSharedCheck_1518_ = !lean_is_exclusive(v_l_1075_);
if (v_isSharedCheck_1518_ == 0)
{
lean_object* v_unused_1519_; lean_object* v_unused_1520_; lean_object* v_unused_1521_; lean_object* v_unused_1522_; lean_object* v_unused_1523_; 
v_unused_1519_ = lean_ctor_get(v_l_1075_, 4);
lean_dec(v_unused_1519_);
v_unused_1520_ = lean_ctor_get(v_l_1075_, 3);
lean_dec(v_unused_1520_);
v_unused_1521_ = lean_ctor_get(v_l_1075_, 2);
lean_dec(v_unused_1521_);
v_unused_1522_ = lean_ctor_get(v_l_1075_, 1);
lean_dec(v_unused_1522_);
v_unused_1523_ = lean_ctor_get(v_l_1075_, 0);
lean_dec(v_unused_1523_);
v___x_1496_ = v_l_1075_;
v_isShared_1497_ = v_isSharedCheck_1518_;
goto v_resetjp_1495_;
}
else
{
lean_dec(v_l_1075_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1518_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
if (lean_obj_tag(v_r_1259_) == 0)
{
lean_object* v_k_1498_; lean_object* v_v_1499_; lean_object* v_size_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1504_; 
v_k_1498_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_k_1498_);
v_v_1499_ = lean_ctor_get(v___x_1411_, 1);
lean_inc(v_v_1499_);
lean_dec_ref(v___x_1411_);
v_size_1500_ = lean_ctor_get(v_r_1259_, 0);
v___x_1501_ = lean_nat_add(v___x_1265_, v_size_1255_);
lean_dec(v_size_1255_);
v___x_1502_ = lean_nat_add(v___x_1265_, v_size_1500_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v_tree_1412_);
lean_ctor_set(v___x_1409_, 3, v_r_1259_);
lean_ctor_set(v___x_1409_, 2, v_v_1499_);
lean_ctor_set(v___x_1409_, 1, v_k_1498_);
lean_ctor_set(v___x_1409_, 0, v___x_1502_);
v___x_1504_ = v___x_1409_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1502_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_k_1498_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_v_1499_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_r_1259_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v_tree_1412_);
v___x_1504_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
lean_object* v___x_1506_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 4, v___x_1504_);
lean_ctor_set(v___x_1496_, 0, v___x_1501_);
v___x_1506_ = v___x_1496_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1507_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1507_, 3, v_l_1258_);
lean_ctor_set(v_reuseFailAlloc_1507_, 4, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
else
{
lean_object* v_k_1509_; lean_object* v_v_1510_; lean_object* v___x_1511_; lean_object* v___x_1513_; 
lean_dec(v_size_1255_);
v_k_1509_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_k_1509_);
v_v_1510_ = lean_ctor_get(v___x_1411_, 1);
lean_inc(v_v_1510_);
lean_dec_ref(v___x_1411_);
v___x_1511_ = lean_unsigned_to_nat(3u);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v_r_1259_);
lean_ctor_set(v___x_1409_, 3, v_r_1259_);
lean_ctor_set(v___x_1409_, 2, v_v_1510_);
lean_ctor_set(v___x_1409_, 1, v_k_1509_);
lean_ctor_set(v___x_1409_, 0, v___x_1265_);
v___x_1513_ = v___x_1409_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_k_1509_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_v_1510_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v_r_1259_);
lean_ctor_set(v_reuseFailAlloc_1517_, 4, v_r_1259_);
v___x_1513_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1515_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 4, v___x_1513_);
lean_ctor_set(v___x_1496_, 0, v___x_1511_);
v___x_1515_ = v___x_1496_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1511_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1516_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1516_, 3, v_l_1258_);
lean_ctor_set(v_reuseFailAlloc_1516_, 4, v___x_1513_);
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
}
else
{
if (lean_obj_tag(v_r_1259_) == 0)
{
lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1548_; 
lean_inc(v_l_1258_);
lean_inc(v_v_1257_);
lean_inc(v_k_1256_);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_l_1075_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; lean_object* v_unused_1550_; lean_object* v_unused_1551_; lean_object* v_unused_1552_; lean_object* v_unused_1553_; 
v_unused_1549_ = lean_ctor_get(v_l_1075_, 4);
lean_dec(v_unused_1549_);
v_unused_1550_ = lean_ctor_get(v_l_1075_, 3);
lean_dec(v_unused_1550_);
v_unused_1551_ = lean_ctor_get(v_l_1075_, 2);
lean_dec(v_unused_1551_);
v_unused_1552_ = lean_ctor_get(v_l_1075_, 1);
lean_dec(v_unused_1552_);
v_unused_1553_ = lean_ctor_get(v_l_1075_, 0);
lean_dec(v_unused_1553_);
v___x_1525_ = v_l_1075_;
v_isShared_1526_ = v_isSharedCheck_1548_;
goto v_resetjp_1524_;
}
else
{
lean_dec(v_l_1075_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1548_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v_k_1527_; lean_object* v_v_1528_; lean_object* v_k_1529_; lean_object* v_v_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1544_; 
v_k_1527_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_k_1527_);
v_v_1528_ = lean_ctor_get(v___x_1411_, 1);
lean_inc(v_v_1528_);
lean_dec_ref(v___x_1411_);
v_k_1529_ = lean_ctor_get(v_r_1259_, 1);
v_v_1530_ = lean_ctor_get(v_r_1259_, 2);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_r_1259_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; lean_object* v_unused_1546_; lean_object* v_unused_1547_; 
v_unused_1545_ = lean_ctor_get(v_r_1259_, 4);
lean_dec(v_unused_1545_);
v_unused_1546_ = lean_ctor_get(v_r_1259_, 3);
lean_dec(v_unused_1546_);
v_unused_1547_ = lean_ctor_get(v_r_1259_, 0);
lean_dec(v_unused_1547_);
v___x_1532_ = v_r_1259_;
v_isShared_1533_ = v_isSharedCheck_1544_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_v_1530_);
lean_inc(v_k_1529_);
lean_dec(v_r_1259_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1544_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1534_ = lean_unsigned_to_nat(3u);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 4, v_l_1258_);
lean_ctor_set(v___x_1532_, 3, v_l_1258_);
lean_ctor_set(v___x_1532_, 2, v_v_1257_);
lean_ctor_set(v___x_1532_, 1, v_k_1256_);
lean_ctor_set(v___x_1532_, 0, v___x_1265_);
v___x_1536_ = v___x_1532_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1543_, 3, v_l_1258_);
lean_ctor_set(v_reuseFailAlloc_1543_, 4, v_l_1258_);
v___x_1536_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1538_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v_l_1258_);
lean_ctor_set(v___x_1409_, 3, v_l_1258_);
lean_ctor_set(v___x_1409_, 2, v_v_1528_);
lean_ctor_set(v___x_1409_, 1, v_k_1527_);
lean_ctor_set(v___x_1409_, 0, v___x_1265_);
v___x_1538_ = v___x_1409_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_k_1527_);
lean_ctor_set(v_reuseFailAlloc_1542_, 2, v_v_1528_);
lean_ctor_set(v_reuseFailAlloc_1542_, 3, v_l_1258_);
lean_ctor_set(v_reuseFailAlloc_1542_, 4, v_l_1258_);
v___x_1538_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1540_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 4, v___x_1538_);
lean_ctor_set(v___x_1525_, 3, v___x_1536_);
lean_ctor_set(v___x_1525_, 2, v_v_1530_);
lean_ctor_set(v___x_1525_, 1, v_k_1529_);
lean_ctor_set(v___x_1525_, 0, v___x_1534_);
v___x_1540_ = v___x_1525_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1534_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_k_1529_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v_v_1530_);
lean_ctor_set(v_reuseFailAlloc_1541_, 3, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1541_, 4, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
}
else
{
lean_object* v_k_1554_; lean_object* v_v_1555_; lean_object* v___x_1556_; lean_object* v___x_1558_; 
v_k_1554_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_k_1554_);
v_v_1555_ = lean_ctor_get(v___x_1411_, 1);
lean_inc(v_v_1555_);
lean_dec_ref(v___x_1411_);
v___x_1556_ = lean_unsigned_to_nat(2u);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 4, v_r_1259_);
lean_ctor_set(v___x_1409_, 3, v_l_1075_);
lean_ctor_set(v___x_1409_, 2, v_v_1555_);
lean_ctor_set(v___x_1409_, 1, v_k_1554_);
lean_ctor_set(v___x_1409_, 0, v___x_1556_);
v___x_1558_ = v___x_1409_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_k_1554_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_v_1555_);
lean_ctor_set(v_reuseFailAlloc_1559_, 3, v_l_1075_);
lean_ctor_set(v_reuseFailAlloc_1559_, 4, v_r_1259_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
}
}
}
else
{
return v_l_1075_;
}
}
else
{
return v_r_1076_;
}
}
default: 
{
lean_object* v_impl_1566_; lean_object* v___x_1567_; 
v_impl_1566_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1071_, v_r_1076_);
v___x_1567_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1566_) == 0)
{
if (lean_obj_tag(v_l_1075_) == 0)
{
lean_object* v_size_1568_; lean_object* v_size_1569_; lean_object* v_k_1570_; lean_object* v_v_1571_; lean_object* v_l_1572_; lean_object* v_r_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; 
v_size_1568_ = lean_ctor_get(v_impl_1566_, 0);
v_size_1569_ = lean_ctor_get(v_l_1075_, 0);
v_k_1570_ = lean_ctor_get(v_l_1075_, 1);
v_v_1571_ = lean_ctor_get(v_l_1075_, 2);
v_l_1572_ = lean_ctor_get(v_l_1075_, 3);
v_r_1573_ = lean_ctor_get(v_l_1075_, 4);
lean_inc(v_r_1573_);
v___x_1574_ = lean_unsigned_to_nat(3u);
v___x_1575_ = lean_nat_mul(v___x_1574_, v_size_1568_);
v___x_1576_ = lean_nat_dec_lt(v___x_1575_, v_size_1569_);
lean_dec(v___x_1575_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
lean_dec(v_r_1573_);
v___x_1577_ = lean_nat_add(v___x_1567_, v_size_1569_);
v___x_1578_ = lean_nat_add(v___x_1577_, v_size_1568_);
lean_dec(v___x_1577_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 4, v_impl_1566_);
lean_ctor_set(v___x_1078_, 0, v___x_1578_);
v___x_1580_ = v___x_1078_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_k_1073_);
lean_ctor_set(v_reuseFailAlloc_1581_, 2, v_v_1074_);
lean_ctor_set(v_reuseFailAlloc_1581_, 3, v_l_1075_);
lean_ctor_set(v_reuseFailAlloc_1581_, 4, v_impl_1566_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
else
{
lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1647_; 
lean_inc(v_l_1572_);
lean_inc(v_v_1571_);
lean_inc(v_k_1570_);
lean_inc(v_size_1569_);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_l_1075_);
if (v_isSharedCheck_1647_ == 0)
{
lean_object* v_unused_1648_; lean_object* v_unused_1649_; lean_object* v_unused_1650_; lean_object* v_unused_1651_; lean_object* v_unused_1652_; 
v_unused_1648_ = lean_ctor_get(v_l_1075_, 4);
lean_dec(v_unused_1648_);
v_unused_1649_ = lean_ctor_get(v_l_1075_, 3);
lean_dec(v_unused_1649_);
v_unused_1650_ = lean_ctor_get(v_l_1075_, 2);
lean_dec(v_unused_1650_);
v_unused_1651_ = lean_ctor_get(v_l_1075_, 1);
lean_dec(v_unused_1651_);
v_unused_1652_ = lean_ctor_get(v_l_1075_, 0);
lean_dec(v_unused_1652_);
v___x_1583_ = v_l_1075_;
v_isShared_1584_ = v_isSharedCheck_1647_;
goto v_resetjp_1582_;
}
else
{
lean_dec(v_l_1075_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1647_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v_size_1585_; lean_object* v_size_1586_; lean_object* v_k_1587_; lean_object* v_v_1588_; lean_object* v_l_1589_; lean_object* v_r_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v_size_1585_ = lean_ctor_get(v_l_1572_, 0);
v_size_1586_ = lean_ctor_get(v_r_1573_, 0);
v_k_1587_ = lean_ctor_get(v_r_1573_, 1);
v_v_1588_ = lean_ctor_get(v_r_1573_, 2);
v_l_1589_ = lean_ctor_get(v_r_1573_, 3);
v_r_1590_ = lean_ctor_get(v_r_1573_, 4);
v___x_1591_ = lean_unsigned_to_nat(2u);
v___x_1592_ = lean_nat_mul(v___x_1591_, v_size_1585_);
v___x_1593_ = lean_nat_dec_lt(v_size_1586_, v___x_1592_);
lean_dec(v___x_1592_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1622_; 
lean_inc(v_r_1590_);
lean_inc(v_l_1589_);
lean_inc(v_v_1588_);
lean_inc(v_k_1587_);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_r_1573_);
if (v_isSharedCheck_1622_ == 0)
{
lean_object* v_unused_1623_; lean_object* v_unused_1624_; lean_object* v_unused_1625_; lean_object* v_unused_1626_; lean_object* v_unused_1627_; 
v_unused_1623_ = lean_ctor_get(v_r_1573_, 4);
lean_dec(v_unused_1623_);
v_unused_1624_ = lean_ctor_get(v_r_1573_, 3);
lean_dec(v_unused_1624_);
v_unused_1625_ = lean_ctor_get(v_r_1573_, 2);
lean_dec(v_unused_1625_);
v_unused_1626_ = lean_ctor_get(v_r_1573_, 1);
lean_dec(v_unused_1626_);
v_unused_1627_ = lean_ctor_get(v_r_1573_, 0);
lean_dec(v_unused_1627_);
v___x_1595_ = v_r_1573_;
v_isShared_1596_ = v_isSharedCheck_1622_;
goto v_resetjp_1594_;
}
else
{
lean_dec(v_r_1573_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1622_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___y_1600_; lean_object* v___y_1601_; lean_object* v___y_1602_; lean_object* v___x_1610_; lean_object* v___y_1612_; 
v___x_1597_ = lean_nat_add(v___x_1567_, v_size_1569_);
lean_dec(v_size_1569_);
v___x_1598_ = lean_nat_add(v___x_1597_, v_size_1568_);
lean_dec(v___x_1597_);
v___x_1610_ = lean_nat_add(v___x_1567_, v_size_1585_);
if (lean_obj_tag(v_l_1589_) == 0)
{
lean_object* v_size_1620_; 
v_size_1620_ = lean_ctor_get(v_l_1589_, 0);
lean_inc(v_size_1620_);
v___y_1612_ = v_size_1620_;
goto v___jp_1611_;
}
else
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_unsigned_to_nat(0u);
v___y_1612_ = v___x_1621_;
goto v___jp_1611_;
}
v___jp_1599_:
{
lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1603_ = lean_nat_add(v___y_1600_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec(v___y_1600_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 4, v_impl_1566_);
lean_ctor_set(v___x_1595_, 3, v_r_1590_);
lean_ctor_set(v___x_1595_, 2, v_v_1074_);
lean_ctor_set(v___x_1595_, 1, v_k_1073_);
lean_ctor_set(v___x_1595_, 0, v___x_1603_);
v___x_1605_ = v___x_1595_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_k_1073_);
lean_ctor_set(v_reuseFailAlloc_1609_, 2, v_v_1074_);
lean_ctor_set(v_reuseFailAlloc_1609_, 3, v_r_1590_);
lean_ctor_set(v_reuseFailAlloc_1609_, 4, v_impl_1566_);
v___x_1605_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1607_; 
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 4, v___x_1605_);
lean_ctor_set(v___x_1583_, 3, v___y_1601_);
lean_ctor_set(v___x_1583_, 2, v_v_1588_);
lean_ctor_set(v___x_1583_, 1, v_k_1587_);
lean_ctor_set(v___x_1583_, 0, v___x_1598_);
v___x_1607_ = v___x_1583_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_k_1587_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v_v_1588_);
lean_ctor_set(v_reuseFailAlloc_1608_, 3, v___y_1601_);
lean_ctor_set(v_reuseFailAlloc_1608_, 4, v___x_1605_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
v___jp_1611_:
{
lean_object* v___x_1613_; lean_object* v___x_1615_; 
v___x_1613_ = lean_nat_add(v___x_1610_, v___y_1612_);
lean_dec(v___y_1612_);
lean_dec(v___x_1610_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 4, v_l_1589_);
lean_ctor_set(v___x_1078_, 3, v_l_1572_);
lean_ctor_set(v___x_1078_, 2, v_v_1571_);
lean_ctor_set(v___x_1078_, 1, v_k_1570_);
lean_ctor_set(v___x_1078_, 0, v___x_1613_);
v___x_1615_ = v___x_1078_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1613_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_k_1570_);
lean_ctor_set(v_reuseFailAlloc_1619_, 2, v_v_1571_);
lean_ctor_set(v_reuseFailAlloc_1619_, 3, v_l_1572_);
lean_ctor_set(v_reuseFailAlloc_1619_, 4, v_l_1589_);
v___x_1615_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_nat_add(v___x_1567_, v_size_1568_);
if (lean_obj_tag(v_r_1590_) == 0)
{
lean_object* v_size_1617_; 
v_size_1617_ = lean_ctor_get(v_r_1590_, 0);
lean_inc(v_size_1617_);
v___y_1600_ = v___x_1616_;
v___y_1601_ = v___x_1615_;
v___y_1602_ = v_size_1617_;
goto v___jp_1599_;
}
else
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_unsigned_to_nat(0u);
v___y_1600_ = v___x_1616_;
v___y_1601_ = v___x_1615_;
v___y_1602_ = v___x_1618_;
goto v___jp_1599_;
}
}
}
}
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1633_; 
lean_del_object(v___x_1078_);
v___x_1628_ = lean_nat_add(v___x_1567_, v_size_1569_);
lean_dec(v_size_1569_);
v___x_1629_ = lean_nat_add(v___x_1628_, v_size_1568_);
lean_dec(v___x_1628_);
v___x_1630_ = lean_nat_add(v___x_1567_, v_size_1568_);
v___x_1631_ = lean_nat_add(v___x_1630_, v_size_1586_);
lean_dec(v___x_1630_);
lean_inc_ref(v_impl_1566_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 4, v_impl_1566_);
lean_ctor_set(v___x_1583_, 3, v_r_1573_);
lean_ctor_set(v___x_1583_, 2, v_v_1074_);
lean_ctor_set(v___x_1583_, 1, v_k_1073_);
lean_ctor_set(v___x_1583_, 0, v___x_1631_);
v___x_1633_ = v___x_1583_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_k_1073_);
lean_ctor_set(v_reuseFailAlloc_1646_, 2, v_v_1074_);
lean_ctor_set(v_reuseFailAlloc_1646_, 3, v_r_1573_);
lean_ctor_set(v_reuseFailAlloc_1646_, 4, v_impl_1566_);
v___x_1633_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
v_isSharedCheck_1640_ = !lean_is_exclusive(v_impl_1566_);
if (v_isSharedCheck_1640_ == 0)
{
lean_object* v_unused_1641_; lean_object* v_unused_1642_; lean_object* v_unused_1643_; lean_object* v_unused_1644_; lean_object* v_unused_1645_; 
v_unused_1641_ = lean_ctor_get(v_impl_1566_, 4);
lean_dec(v_unused_1641_);
v_unused_1642_ = lean_ctor_get(v_impl_1566_, 3);
lean_dec(v_unused_1642_);
v_unused_1643_ = lean_ctor_get(v_impl_1566_, 2);
lean_dec(v_unused_1643_);
v_unused_1644_ = lean_ctor_get(v_impl_1566_, 1);
lean_dec(v_unused_1644_);
v_unused_1645_ = lean_ctor_get(v_impl_1566_, 0);
lean_dec(v_unused_1645_);
v___x_1635_ = v_impl_1566_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_dec(v_impl_1566_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 4, v___x_1633_);
lean_ctor_set(v___x_1635_, 3, v_l_1572_);
lean_ctor_set(v___x_1635_, 2, v_v_1571_);
lean_ctor_set(v___x_1635_, 1, v_k_1570_);
lean_ctor_set(v___x_1635_, 0, v___x_1629_);
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1629_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_k_1570_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v_v_1571_);
lean_ctor_set(v_reuseFailAlloc_1639_, 3, v_l_1572_);
lean_ctor_set(v_reuseFailAlloc_1639_, 4, v___x_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1653_; lean_object* v___x_1654_; lean_object* v___x_1656_; 
v_size_1653_ = lean_ctor_get(v_impl_1566_, 0);
v___x_1654_ = lean_nat_add(v___x_1567_, v_size_1653_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 4, v_impl_1566_);
lean_ctor_set(v___x_1078_, 0, v___x_1654_);
v___x_1656_ = v___x_1078_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_k_1073_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v_v_1074_);
lean_ctor_set(v_reuseFailAlloc_1657_, 3, v_l_1075_);
lean_ctor_set(v_reuseFailAlloc_1657_, 4, v_impl_1566_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
else
{
if (lean_obj_tag(v_l_1075_) == 0)
{
lean_object* v_l_1658_; 
v_l_1658_ = lean_ctor_get(v_l_1075_, 3);
if (lean_obj_tag(v_l_1658_) == 0)
{
lean_object* v_r_1659_; 
lean_inc_ref(v_l_1658_);
v_r_1659_ = lean_ctor_get(v_l_1075_, 4);
lean_inc(v_r_1659_);
if (lean_obj_tag(v_r_1659_) == 0)
{
lean_object* v_size_1660_; lean_object* v_k_1661_; lean_object* v_v_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1675_; 
v_size_1660_ = lean_ctor_get(v_l_1075_, 0);
v_k_1661_ = lean_ctor_get(v_l_1075_, 1);
v_v_1662_ = lean_ctor_get(v_l_1075_, 2);
v_isSharedCheck_1675_ = !lean_is_exclusive(v_l_1075_);
if (v_isSharedCheck_1675_ == 0)
{
lean_object* v_unused_1676_; lean_object* v_unused_1677_; 
v_unused_1676_ = lean_ctor_get(v_l_1075_, 4);
lean_dec(v_unused_1676_);
v_unused_1677_ = lean_ctor_get(v_l_1075_, 3);
lean_dec(v_unused_1677_);
v___x_1664_ = v_l_1075_;
v_isShared_1665_ = v_isSharedCheck_1675_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_v_1662_);
lean_inc(v_k_1661_);
lean_inc(v_size_1660_);
lean_dec(v_l_1075_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1675_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v_size_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
v_size_1666_ = lean_ctor_get(v_r_1659_, 0);
v___x_1667_ = lean_nat_add(v___x_1567_, v_size_1660_);
lean_dec(v_size_1660_);
v___x_1668_ = lean_nat_add(v___x_1567_, v_size_1666_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 4, v_impl_1566_);
lean_ctor_set(v___x_1664_, 3, v_r_1659_);
lean_ctor_set(v___x_1664_, 2, v_v_1074_);
lean_ctor_set(v___x_1664_, 1, v_k_1073_);
lean_ctor_set(v___x_1664_, 0, v___x_1668_);
v___x_1670_ = v___x_1664_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1668_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_k_1073_);
lean_ctor_set(v_reuseFailAlloc_1674_, 2, v_v_1074_);
lean_ctor_set(v_reuseFailAlloc_1674_, 3, v_r_1659_);
lean_ctor_set(v_reuseFailAlloc_1674_, 4, v_impl_1566_);
v___x_1670_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1672_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 4, v___x_1670_);
lean_ctor_set(v___x_1078_, 3, v_l_1658_);
lean_ctor_set(v___x_1078_, 2, v_v_1662_);
lean_ctor_set(v___x_1078_, 1, v_k_1661_);
lean_ctor_set(v___x_1078_, 0, v___x_1667_);
v___x_1672_ = v___x_1078_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_k_1661_);
lean_ctor_set(v_reuseFailAlloc_1673_, 2, v_v_1662_);
lean_ctor_set(v_reuseFailAlloc_1673_, 3, v_l_1658_);
lean_ctor_set(v_reuseFailAlloc_1673_, 4, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
else
{
lean_object* v_k_1678_; lean_object* v_v_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1690_; 
v_k_1678_ = lean_ctor_get(v_l_1075_, 1);
v_v_1679_ = lean_ctor_get(v_l_1075_, 2);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_l_1075_);
if (v_isSharedCheck_1690_ == 0)
{
lean_object* v_unused_1691_; lean_object* v_unused_1692_; lean_object* v_unused_1693_; 
v_unused_1691_ = lean_ctor_get(v_l_1075_, 4);
lean_dec(v_unused_1691_);
v_unused_1692_ = lean_ctor_get(v_l_1075_, 3);
lean_dec(v_unused_1692_);
v_unused_1693_ = lean_ctor_get(v_l_1075_, 0);
lean_dec(v_unused_1693_);
v___x_1681_ = v_l_1075_;
v_isShared_1682_ = v_isSharedCheck_1690_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_v_1679_);
lean_inc(v_k_1678_);
lean_dec(v_l_1075_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1690_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1683_ = lean_unsigned_to_nat(3u);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 3, v_r_1659_);
lean_ctor_set(v___x_1681_, 2, v_v_1074_);
lean_ctor_set(v___x_1681_, 1, v_k_1073_);
lean_ctor_set(v___x_1681_, 0, v___x_1567_);
v___x_1685_ = v___x_1681_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1689_, 1, v_k_1073_);
lean_ctor_set(v_reuseFailAlloc_1689_, 2, v_v_1074_);
lean_ctor_set(v_reuseFailAlloc_1689_, 3, v_r_1659_);
lean_ctor_set(v_reuseFailAlloc_1689_, 4, v_r_1659_);
v___x_1685_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1687_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 4, v___x_1685_);
lean_ctor_set(v___x_1078_, 3, v_l_1658_);
lean_ctor_set(v___x_1078_, 2, v_v_1679_);
lean_ctor_set(v___x_1078_, 1, v_k_1678_);
lean_ctor_set(v___x_1078_, 0, v___x_1683_);
v___x_1687_ = v___x_1078_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_k_1678_);
lean_ctor_set(v_reuseFailAlloc_1688_, 2, v_v_1679_);
lean_ctor_set(v_reuseFailAlloc_1688_, 3, v_l_1658_);
lean_ctor_set(v_reuseFailAlloc_1688_, 4, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
else
{
lean_object* v_r_1694_; 
v_r_1694_ = lean_ctor_get(v_l_1075_, 4);
lean_inc(v_r_1694_);
if (lean_obj_tag(v_r_1694_) == 0)
{
lean_object* v_k_1695_; lean_object* v_v_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1719_; 
lean_inc(v_l_1658_);
v_k_1695_ = lean_ctor_get(v_l_1075_, 1);
v_v_1696_ = lean_ctor_get(v_l_1075_, 2);
v_isSharedCheck_1719_ = !lean_is_exclusive(v_l_1075_);
if (v_isSharedCheck_1719_ == 0)
{
lean_object* v_unused_1720_; lean_object* v_unused_1721_; lean_object* v_unused_1722_; 
v_unused_1720_ = lean_ctor_get(v_l_1075_, 4);
lean_dec(v_unused_1720_);
v_unused_1721_ = lean_ctor_get(v_l_1075_, 3);
lean_dec(v_unused_1721_);
v_unused_1722_ = lean_ctor_get(v_l_1075_, 0);
lean_dec(v_unused_1722_);
v___x_1698_ = v_l_1075_;
v_isShared_1699_ = v_isSharedCheck_1719_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_v_1696_);
lean_inc(v_k_1695_);
lean_dec(v_l_1075_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1719_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v_k_1700_; lean_object* v_v_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1715_; 
v_k_1700_ = lean_ctor_get(v_r_1694_, 1);
v_v_1701_ = lean_ctor_get(v_r_1694_, 2);
v_isSharedCheck_1715_ = !lean_is_exclusive(v_r_1694_);
if (v_isSharedCheck_1715_ == 0)
{
lean_object* v_unused_1716_; lean_object* v_unused_1717_; lean_object* v_unused_1718_; 
v_unused_1716_ = lean_ctor_get(v_r_1694_, 4);
lean_dec(v_unused_1716_);
v_unused_1717_ = lean_ctor_get(v_r_1694_, 3);
lean_dec(v_unused_1717_);
v_unused_1718_ = lean_ctor_get(v_r_1694_, 0);
lean_dec(v_unused_1718_);
v___x_1703_ = v_r_1694_;
v_isShared_1704_ = v_isSharedCheck_1715_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_v_1701_);
lean_inc(v_k_1700_);
lean_dec(v_r_1694_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1715_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v___x_1707_; 
v___x_1705_ = lean_unsigned_to_nat(3u);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 4, v_l_1658_);
lean_ctor_set(v___x_1703_, 3, v_l_1658_);
lean_ctor_set(v___x_1703_, 2, v_v_1696_);
lean_ctor_set(v___x_1703_, 1, v_k_1695_);
lean_ctor_set(v___x_1703_, 0, v___x_1567_);
v___x_1707_ = v___x_1703_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_k_1695_);
lean_ctor_set(v_reuseFailAlloc_1714_, 2, v_v_1696_);
lean_ctor_set(v_reuseFailAlloc_1714_, 3, v_l_1658_);
lean_ctor_set(v_reuseFailAlloc_1714_, 4, v_l_1658_);
v___x_1707_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1709_; 
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 4, v_l_1658_);
lean_ctor_set(v___x_1698_, 2, v_v_1074_);
lean_ctor_set(v___x_1698_, 1, v_k_1073_);
lean_ctor_set(v___x_1698_, 0, v___x_1567_);
v___x_1709_ = v___x_1698_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_k_1073_);
lean_ctor_set(v_reuseFailAlloc_1713_, 2, v_v_1074_);
lean_ctor_set(v_reuseFailAlloc_1713_, 3, v_l_1658_);
lean_ctor_set(v_reuseFailAlloc_1713_, 4, v_l_1658_);
v___x_1709_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
lean_object* v___x_1711_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 4, v___x_1709_);
lean_ctor_set(v___x_1078_, 3, v___x_1707_);
lean_ctor_set(v___x_1078_, 2, v_v_1701_);
lean_ctor_set(v___x_1078_, 1, v_k_1700_);
lean_ctor_set(v___x_1078_, 0, v___x_1705_);
v___x_1711_ = v___x_1078_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1705_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_k_1700_);
lean_ctor_set(v_reuseFailAlloc_1712_, 2, v_v_1701_);
lean_ctor_set(v_reuseFailAlloc_1712_, 3, v___x_1707_);
lean_ctor_set(v_reuseFailAlloc_1712_, 4, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
}
}
else
{
lean_object* v___x_1723_; lean_object* v___x_1725_; 
v___x_1723_ = lean_unsigned_to_nat(2u);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 4, v_r_1694_);
lean_ctor_set(v___x_1078_, 0, v___x_1723_);
v___x_1725_ = v___x_1078_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1723_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_k_1073_);
lean_ctor_set(v_reuseFailAlloc_1726_, 2, v_v_1074_);
lean_ctor_set(v_reuseFailAlloc_1726_, 3, v_l_1075_);
lean_ctor_set(v_reuseFailAlloc_1726_, 4, v_r_1694_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
else
{
lean_object* v___x_1728_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 4, v_l_1075_);
lean_ctor_set(v___x_1078_, 0, v___x_1567_);
v___x_1728_ = v___x_1078_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_k_1073_);
lean_ctor_set(v_reuseFailAlloc_1729_, 2, v_v_1074_);
lean_ctor_set(v_reuseFailAlloc_1729_, 3, v_l_1075_);
lean_ctor_set(v_reuseFailAlloc_1729_, 4, v_l_1075_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
}
}
}
else
{
return v_t_1072_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object* v_k_1732_, lean_object* v_t_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1732_, v_t_1733_);
lean_dec(v_k_1732_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object* v_ext_1735_, lean_object* v_declName_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v_ext_1742_; lean_object* v_toEnvExtension_1743_; lean_object* v_env_1744_; lean_object* v_asyncMode_1745_; lean_object* v___x_1746_; lean_object* v___y_1748_; lean_object* v_funCC_1775_; uint8_t v___x_1776_; 
v___x_1740_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1741_ = lean_st_ref_get(v_a_1738_);
v_ext_1742_ = lean_ctor_get(v_ext_1735_, 1);
v_toEnvExtension_1743_ = lean_ctor_get(v_ext_1742_, 0);
v_env_1744_ = lean_ctor_get(v___x_1741_, 0);
lean_inc_ref(v_env_1744_);
lean_dec(v___x_1741_);
v_asyncMode_1745_ = lean_ctor_get(v_toEnvExtension_1743_, 2);
v___x_1746_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1740_, v_ext_1735_, v_env_1744_, v_asyncMode_1745_);
v_funCC_1775_ = lean_ctor_get(v___x_1746_, 2);
v___x_1776_ = l_Lean_NameSet_contains(v_funCC_1775_, v_declName_1736_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; 
lean_inc(v_declName_1736_);
v___x_1777_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_1736_, v_a_1737_, v_a_1738_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_dec_ref_known(v___x_1777_, 1);
v___y_1748_ = v_a_1738_;
goto v___jp_1747_;
}
else
{
lean_dec(v___x_1746_);
lean_dec(v_declName_1736_);
lean_dec_ref(v_ext_1735_);
return v___x_1777_;
}
}
else
{
v___y_1748_ = v_a_1738_;
goto v___jp_1747_;
}
v___jp_1747_:
{
lean_object* v_funCC_1749_; lean_object* v___x_1750_; lean_object* v___f_1751_; lean_object* v___x_1752_; lean_object* v_env_1753_; lean_object* v_nextMacroScope_1754_; lean_object* v_ngen_1755_; lean_object* v_auxDeclNGen_1756_; lean_object* v_traceState_1757_; lean_object* v_recordedDeps_1758_; lean_object* v_messages_1759_; lean_object* v_infoState_1760_; lean_object* v_snapshotTasks_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1773_; 
v_funCC_1749_ = lean_ctor_get(v___x_1746_, 2);
lean_inc(v_funCC_1749_);
lean_dec(v___x_1746_);
v___x_1750_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_declName_1736_, v_funCC_1749_);
lean_dec(v_declName_1736_);
v___f_1751_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0), 2, 1);
lean_closure_set(v___f_1751_, 0, v___x_1750_);
v___x_1752_ = lean_st_ref_take(v___y_1748_);
v_env_1753_ = lean_ctor_get(v___x_1752_, 0);
v_nextMacroScope_1754_ = lean_ctor_get(v___x_1752_, 1);
v_ngen_1755_ = lean_ctor_get(v___x_1752_, 2);
v_auxDeclNGen_1756_ = lean_ctor_get(v___x_1752_, 3);
v_traceState_1757_ = lean_ctor_get(v___x_1752_, 4);
v_recordedDeps_1758_ = lean_ctor_get(v___x_1752_, 6);
v_messages_1759_ = lean_ctor_get(v___x_1752_, 7);
v_infoState_1760_ = lean_ctor_get(v___x_1752_, 8);
v_snapshotTasks_1761_ = lean_ctor_get(v___x_1752_, 9);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1773_ == 0)
{
lean_object* v_unused_1774_; 
v_unused_1774_ = lean_ctor_get(v___x_1752_, 5);
lean_dec(v_unused_1774_);
v___x_1763_ = v___x_1752_;
v_isShared_1764_ = v_isSharedCheck_1773_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_snapshotTasks_1761_);
lean_inc(v_infoState_1760_);
lean_inc(v_messages_1759_);
lean_inc(v_recordedDeps_1758_);
lean_inc(v_traceState_1757_);
lean_inc(v_auxDeclNGen_1756_);
lean_inc(v_ngen_1755_);
lean_inc(v_nextMacroScope_1754_);
lean_inc(v_env_1753_);
lean_dec(v___x_1752_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1773_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1765_ = lean_box(0);
v___x_1766_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1735_, v_env_1753_, v___f_1751_);
v___x_1767_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 5, v___x_1767_);
lean_ctor_set(v___x_1763_, 0, v___x_1766_);
v___x_1769_ = v___x_1763_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1766_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v_nextMacroScope_1754_);
lean_ctor_set(v_reuseFailAlloc_1772_, 2, v_ngen_1755_);
lean_ctor_set(v_reuseFailAlloc_1772_, 3, v_auxDeclNGen_1756_);
lean_ctor_set(v_reuseFailAlloc_1772_, 4, v_traceState_1757_);
lean_ctor_set(v_reuseFailAlloc_1772_, 5, v___x_1767_);
lean_ctor_set(v_reuseFailAlloc_1772_, 6, v_recordedDeps_1758_);
lean_ctor_set(v_reuseFailAlloc_1772_, 7, v_messages_1759_);
lean_ctor_set(v_reuseFailAlloc_1772_, 8, v_infoState_1760_);
lean_ctor_set(v_reuseFailAlloc_1772_, 9, v_snapshotTasks_1761_);
v___x_1769_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_st_ref_put(v___y_1748_, v___x_1769_);
v___x_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1765_);
return v___x_1771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object* v_ext_1778_, lean_object* v_declName_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_1778_, v_declName_1779_, v_a_1780_, v_a_1781_);
lean_dec(v_a_1781_);
lean_dec_ref(v_a_1780_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object* v_00_u03b2_1784_, lean_object* v_k_1785_, lean_object* v_t_1786_, lean_object* v_h_1787_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1785_, v_t_1786_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object* v_00_u03b2_1789_, lean_object* v_k_1790_, lean_object* v_t_1791_, lean_object* v_h_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(v_00_u03b2_1789_, v_k_1790_, v_t_1791_, v_h_1792_);
lean_dec(v_k_1790_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object* v_a_1794_, lean_object* v_s_1795_){
_start:
{
lean_object* v_casesTypes_1796_; lean_object* v_extThms_1797_; lean_object* v_funCC_1798_; lean_object* v_inj_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
v_casesTypes_1796_ = lean_ctor_get(v_s_1795_, 0);
v_extThms_1797_ = lean_ctor_get(v_s_1795_, 1);
v_funCC_1798_ = lean_ctor_get(v_s_1795_, 2);
v_inj_1799_ = lean_ctor_get(v_s_1795_, 4);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_s_1795_);
if (v_isSharedCheck_1806_ == 0)
{
lean_object* v_unused_1807_; 
v_unused_1807_ = lean_ctor_get(v_s_1795_, 3);
lean_dec(v_unused_1807_);
v___x_1801_ = v_s_1795_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_inj_1799_);
lean_inc(v_funCC_1798_);
lean_inc(v_extThms_1797_);
lean_inc(v_casesTypes_1796_);
lean_dec(v_s_1795_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 3, v_a_1794_);
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_casesTypes_1796_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_extThms_1797_);
lean_ctor_set(v_reuseFailAlloc_1805_, 2, v_funCC_1798_);
lean_ctor_set(v_reuseFailAlloc_1805_, 3, v_a_1794_);
lean_ctor_set(v_reuseFailAlloc_1805_, 4, v_inj_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0(void){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0);
v___x_1809_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
lean_ctor_set(v___x_1809_, 2, v___x_1808_);
lean_ctor_set(v___x_1809_, 3, v___x_1808_);
lean_ctor_set(v___x_1809_, 4, v___x_1808_);
lean_ctor_set(v___x_1809_, 5, v___x_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object* v_ext_1810_, lean_object* v_declName_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v_ext_1819_; lean_object* v_toEnvExtension_1820_; lean_object* v_env_1821_; lean_object* v_asyncMode_1822_; lean_object* v___x_1823_; lean_object* v_ematch_1824_; lean_object* v___x_1825_; 
v___x_1817_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1818_ = lean_st_ref_get(v_a_1815_);
v_ext_1819_ = lean_ctor_get(v_ext_1810_, 1);
v_toEnvExtension_1820_ = lean_ctor_get(v_ext_1819_, 0);
v_env_1821_ = lean_ctor_get(v___x_1818_, 0);
lean_inc_ref(v_env_1821_);
lean_dec(v___x_1818_);
v_asyncMode_1822_ = lean_ctor_get(v_toEnvExtension_1820_, 2);
v___x_1823_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1817_, v_ext_1810_, v_env_1821_, v_asyncMode_1822_);
v_ematch_1824_ = lean_ctor_get(v___x_1823_, 3);
lean_inc_ref(v_ematch_1824_);
lean_dec(v___x_1823_);
v___x_1825_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_ematch_1824_, v_declName_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1871_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1828_ = v___x_1825_;
v_isShared_1829_ = v_isSharedCheck_1871_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1825_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1871_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___f_1830_; lean_object* v___x_1831_; lean_object* v_env_1832_; lean_object* v_nextMacroScope_1833_; lean_object* v_ngen_1834_; lean_object* v_auxDeclNGen_1835_; lean_object* v_traceState_1836_; lean_object* v_recordedDeps_1837_; lean_object* v_messages_1838_; lean_object* v_infoState_1839_; lean_object* v_snapshotTasks_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1869_; 
v___f_1830_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0), 2, 1);
lean_closure_set(v___f_1830_, 0, v_a_1826_);
v___x_1831_ = lean_st_ref_take(v_a_1815_);
v_env_1832_ = lean_ctor_get(v___x_1831_, 0);
v_nextMacroScope_1833_ = lean_ctor_get(v___x_1831_, 1);
v_ngen_1834_ = lean_ctor_get(v___x_1831_, 2);
v_auxDeclNGen_1835_ = lean_ctor_get(v___x_1831_, 3);
v_traceState_1836_ = lean_ctor_get(v___x_1831_, 4);
v_recordedDeps_1837_ = lean_ctor_get(v___x_1831_, 6);
v_messages_1838_ = lean_ctor_get(v___x_1831_, 7);
v_infoState_1839_ = lean_ctor_get(v___x_1831_, 8);
v_snapshotTasks_1840_ = lean_ctor_get(v___x_1831_, 9);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1869_ == 0)
{
lean_object* v_unused_1870_; 
v_unused_1870_ = lean_ctor_get(v___x_1831_, 5);
lean_dec(v_unused_1870_);
v___x_1842_ = v___x_1831_;
v_isShared_1843_ = v_isSharedCheck_1869_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_snapshotTasks_1840_);
lean_inc(v_infoState_1839_);
lean_inc(v_messages_1838_);
lean_inc(v_recordedDeps_1837_);
lean_inc(v_traceState_1836_);
lean_inc(v_auxDeclNGen_1835_);
lean_inc(v_ngen_1834_);
lean_inc(v_nextMacroScope_1833_);
lean_inc(v_env_1832_);
lean_dec(v___x_1831_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1869_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1847_; 
v___x_1844_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1810_, v_env_1832_, v___f_1830_);
v___x_1845_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 5, v___x_1845_);
lean_ctor_set(v___x_1842_, 0, v___x_1844_);
v___x_1847_ = v___x_1842_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1844_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v_nextMacroScope_1833_);
lean_ctor_set(v_reuseFailAlloc_1868_, 2, v_ngen_1834_);
lean_ctor_set(v_reuseFailAlloc_1868_, 3, v_auxDeclNGen_1835_);
lean_ctor_set(v_reuseFailAlloc_1868_, 4, v_traceState_1836_);
lean_ctor_set(v_reuseFailAlloc_1868_, 5, v___x_1845_);
lean_ctor_set(v_reuseFailAlloc_1868_, 6, v_recordedDeps_1837_);
lean_ctor_set(v_reuseFailAlloc_1868_, 7, v_messages_1838_);
lean_ctor_set(v_reuseFailAlloc_1868_, 8, v_infoState_1839_);
lean_ctor_set(v_reuseFailAlloc_1868_, 9, v_snapshotTasks_1840_);
v___x_1847_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v_mctx_1850_; lean_object* v_zetaDeltaFVarIds_1851_; lean_object* v_postponed_1852_; lean_object* v_diag_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1866_; 
v___x_1848_ = lean_st_ref_put(v_a_1815_, v___x_1847_);
v___x_1849_ = lean_st_ref_take(v_a_1813_);
v_mctx_1850_ = lean_ctor_get(v___x_1849_, 0);
v_zetaDeltaFVarIds_1851_ = lean_ctor_get(v___x_1849_, 2);
v_postponed_1852_ = lean_ctor_get(v___x_1849_, 3);
v_diag_1853_ = lean_ctor_get(v___x_1849_, 4);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1866_ == 0)
{
lean_object* v_unused_1867_; 
v_unused_1867_ = lean_ctor_get(v___x_1849_, 1);
lean_dec(v_unused_1867_);
v___x_1855_ = v___x_1849_;
v_isShared_1856_ = v_isSharedCheck_1866_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_diag_1853_);
lean_inc(v_postponed_1852_);
lean_inc(v_zetaDeltaFVarIds_1851_);
lean_inc(v_mctx_1850_);
lean_dec(v___x_1849_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1866_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1857_ = lean_box(0);
v___x_1858_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 1, v___x_1858_);
v___x_1860_ = v___x_1855_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_mctx_1850_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v___x_1858_);
lean_ctor_set(v_reuseFailAlloc_1865_, 2, v_zetaDeltaFVarIds_1851_);
lean_ctor_set(v_reuseFailAlloc_1865_, 3, v_postponed_1852_);
lean_ctor_set(v_reuseFailAlloc_1865_, 4, v_diag_1853_);
v___x_1860_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1861_ = lean_st_ref_put(v_a_1813_, v___x_1860_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1857_);
v___x_1863_ = v___x_1828_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1857_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
lean_dec_ref(v_ext_1810_);
v_a_1872_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1825_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1825_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object* v_ext_1880_, lean_object* v_declName_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_1880_, v_declName_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
lean_dec(v_a_1883_);
lean_dec_ref(v_a_1882_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object* v_a_1888_, lean_object* v_s_1889_){
_start:
{
lean_object* v_casesTypes_1890_; lean_object* v_extThms_1891_; lean_object* v_funCC_1892_; lean_object* v_ematch_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
v_casesTypes_1890_ = lean_ctor_get(v_s_1889_, 0);
v_extThms_1891_ = lean_ctor_get(v_s_1889_, 1);
v_funCC_1892_ = lean_ctor_get(v_s_1889_, 2);
v_ematch_1893_ = lean_ctor_get(v_s_1889_, 3);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_s_1889_);
if (v_isSharedCheck_1900_ == 0)
{
lean_object* v_unused_1901_; 
v_unused_1901_ = lean_ctor_get(v_s_1889_, 4);
lean_dec(v_unused_1901_);
v___x_1895_ = v_s_1889_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_ematch_1893_);
lean_inc(v_funCC_1892_);
lean_inc(v_extThms_1891_);
lean_inc(v_casesTypes_1890_);
lean_dec(v_s_1889_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 4, v_a_1888_);
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_casesTypes_1890_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_extThms_1891_);
lean_ctor_set(v_reuseFailAlloc_1899_, 2, v_funCC_1892_);
lean_ctor_set(v_reuseFailAlloc_1899_, 3, v_ematch_1893_);
lean_ctor_set(v_reuseFailAlloc_1899_, 4, v_a_1888_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object* v_ext_1902_, lean_object* v_declName_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v_ext_1911_; lean_object* v_toEnvExtension_1912_; lean_object* v_env_1913_; lean_object* v_asyncMode_1914_; lean_object* v___x_1915_; lean_object* v_inj_1916_; lean_object* v___x_1917_; 
v___x_1909_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1910_ = lean_st_ref_get(v_a_1907_);
v_ext_1911_ = lean_ctor_get(v_ext_1902_, 1);
v_toEnvExtension_1912_ = lean_ctor_get(v_ext_1911_, 0);
v_env_1913_ = lean_ctor_get(v___x_1910_, 0);
lean_inc_ref(v_env_1913_);
lean_dec(v___x_1910_);
v_asyncMode_1914_ = lean_ctor_get(v_toEnvExtension_1912_, 2);
v___x_1915_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1909_, v_ext_1902_, v_env_1913_, v_asyncMode_1914_);
v_inj_1916_ = lean_ctor_get(v___x_1915_, 4);
lean_inc_ref(v_inj_1916_);
lean_dec(v___x_1915_);
v___x_1917_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_inj_1916_, v_declName_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1963_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1920_ = v___x_1917_;
v_isShared_1921_ = v_isSharedCheck_1963_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1917_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1963_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___f_1922_; lean_object* v___x_1923_; lean_object* v_env_1924_; lean_object* v_nextMacroScope_1925_; lean_object* v_ngen_1926_; lean_object* v_auxDeclNGen_1927_; lean_object* v_traceState_1928_; lean_object* v_recordedDeps_1929_; lean_object* v_messages_1930_; lean_object* v_infoState_1931_; lean_object* v_snapshotTasks_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1961_; 
v___f_1922_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0), 2, 1);
lean_closure_set(v___f_1922_, 0, v_a_1918_);
v___x_1923_ = lean_st_ref_take(v_a_1907_);
v_env_1924_ = lean_ctor_get(v___x_1923_, 0);
v_nextMacroScope_1925_ = lean_ctor_get(v___x_1923_, 1);
v_ngen_1926_ = lean_ctor_get(v___x_1923_, 2);
v_auxDeclNGen_1927_ = lean_ctor_get(v___x_1923_, 3);
v_traceState_1928_ = lean_ctor_get(v___x_1923_, 4);
v_recordedDeps_1929_ = lean_ctor_get(v___x_1923_, 6);
v_messages_1930_ = lean_ctor_get(v___x_1923_, 7);
v_infoState_1931_ = lean_ctor_get(v___x_1923_, 8);
v_snapshotTasks_1932_ = lean_ctor_get(v___x_1923_, 9);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1961_ == 0)
{
lean_object* v_unused_1962_; 
v_unused_1962_ = lean_ctor_get(v___x_1923_, 5);
lean_dec(v_unused_1962_);
v___x_1934_ = v___x_1923_;
v_isShared_1935_ = v_isSharedCheck_1961_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_snapshotTasks_1932_);
lean_inc(v_infoState_1931_);
lean_inc(v_messages_1930_);
lean_inc(v_recordedDeps_1929_);
lean_inc(v_traceState_1928_);
lean_inc(v_auxDeclNGen_1927_);
lean_inc(v_ngen_1926_);
lean_inc(v_nextMacroScope_1925_);
lean_inc(v_env_1924_);
lean_dec(v___x_1923_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1961_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1939_; 
v___x_1936_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1902_, v_env_1924_, v___f_1922_);
v___x_1937_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 5, v___x_1937_);
lean_ctor_set(v___x_1934_, 0, v___x_1936_);
v___x_1939_ = v___x_1934_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1936_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v_nextMacroScope_1925_);
lean_ctor_set(v_reuseFailAlloc_1960_, 2, v_ngen_1926_);
lean_ctor_set(v_reuseFailAlloc_1960_, 3, v_auxDeclNGen_1927_);
lean_ctor_set(v_reuseFailAlloc_1960_, 4, v_traceState_1928_);
lean_ctor_set(v_reuseFailAlloc_1960_, 5, v___x_1937_);
lean_ctor_set(v_reuseFailAlloc_1960_, 6, v_recordedDeps_1929_);
lean_ctor_set(v_reuseFailAlloc_1960_, 7, v_messages_1930_);
lean_ctor_set(v_reuseFailAlloc_1960_, 8, v_infoState_1931_);
lean_ctor_set(v_reuseFailAlloc_1960_, 9, v_snapshotTasks_1932_);
v___x_1939_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v_mctx_1942_; lean_object* v_zetaDeltaFVarIds_1943_; lean_object* v_postponed_1944_; lean_object* v_diag_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1958_; 
v___x_1940_ = lean_st_ref_put(v_a_1907_, v___x_1939_);
v___x_1941_ = lean_st_ref_take(v_a_1905_);
v_mctx_1942_ = lean_ctor_get(v___x_1941_, 0);
v_zetaDeltaFVarIds_1943_ = lean_ctor_get(v___x_1941_, 2);
v_postponed_1944_ = lean_ctor_get(v___x_1941_, 3);
v_diag_1945_ = lean_ctor_get(v___x_1941_, 4);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_1958_ == 0)
{
lean_object* v_unused_1959_; 
v_unused_1959_ = lean_ctor_get(v___x_1941_, 1);
lean_dec(v_unused_1959_);
v___x_1947_ = v___x_1941_;
v_isShared_1948_ = v_isSharedCheck_1958_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_diag_1945_);
lean_inc(v_postponed_1944_);
lean_inc(v_zetaDeltaFVarIds_1943_);
lean_inc(v_mctx_1942_);
lean_dec(v___x_1941_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1958_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1952_; 
v___x_1949_ = lean_box(0);
v___x_1950_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 1, v___x_1950_);
v___x_1952_ = v___x_1947_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_mctx_1942_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v___x_1950_);
lean_ctor_set(v_reuseFailAlloc_1957_, 2, v_zetaDeltaFVarIds_1943_);
lean_ctor_set(v_reuseFailAlloc_1957_, 3, v_postponed_1944_);
lean_ctor_set(v_reuseFailAlloc_1957_, 4, v_diag_1945_);
v___x_1952_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1953_ = lean_st_ref_put(v_a_1905_, v___x_1952_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v___x_1949_);
v___x_1955_ = v___x_1920_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1949_);
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
}
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec_ref(v_ext_1902_);
v_a_1964_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1917_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1917_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object* v_ext_1972_, lean_object* v_declName_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_1972_, v_declName_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_);
lean_dec(v_a_1977_);
lean_dec_ref(v_a_1976_);
lean_dec(v_a_1975_);
lean_dec_ref(v_a_1974_);
return v_res_1979_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1980_, lean_object* v_i_1981_, lean_object* v_k_1982_){
_start:
{
lean_object* v___x_1983_; uint8_t v___x_1984_; 
v___x_1983_ = lean_array_get_size(v_keys_1980_);
v___x_1984_ = lean_nat_dec_lt(v_i_1981_, v___x_1983_);
if (v___x_1984_ == 0)
{
lean_dec(v_i_1981_);
return v___x_1984_;
}
else
{
lean_object* v_k_x27_1985_; uint8_t v___x_1986_; 
v_k_x27_1985_ = lean_array_fget_borrowed(v_keys_1980_, v_i_1981_);
v___x_1986_ = lean_name_eq(v_k_1982_, v_k_x27_1985_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = lean_unsigned_to_nat(1u);
v___x_1988_ = lean_nat_add(v_i_1981_, v___x_1987_);
lean_dec(v_i_1981_);
v_i_1981_ = v___x_1988_;
goto _start;
}
else
{
lean_dec(v_i_1981_);
return v___x_1984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1990_, lean_object* v_i_1991_, lean_object* v_k_1992_){
_start:
{
uint8_t v_res_1993_; lean_object* v_r_1994_; 
v_res_1993_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_1990_, v_i_1991_, v_k_1992_);
lean_dec(v_k_1992_);
lean_dec_ref(v_keys_1990_);
v_r_1994_ = lean_box(v_res_1993_);
return v_r_1994_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object* v_x_1995_, size_t v_x_1996_, lean_object* v_x_1997_){
_start:
{
if (lean_obj_tag(v_x_1995_) == 0)
{
lean_object* v_es_1998_; lean_object* v___x_1999_; size_t v___x_2000_; size_t v___x_2001_; lean_object* v_j_2002_; lean_object* v___x_2003_; 
v_es_1998_ = lean_ctor_get(v_x_1995_, 0);
v___x_1999_ = lean_box(2);
v___x_2000_ = ((size_t)31ULL);
v___x_2001_ = lean_usize_land(v_x_1996_, v___x_2000_);
v_j_2002_ = lean_usize_to_nat(v___x_2001_);
v___x_2003_ = lean_array_get_borrowed(v___x_1999_, v_es_1998_, v_j_2002_);
lean_dec(v_j_2002_);
switch(lean_obj_tag(v___x_2003_))
{
case 0:
{
lean_object* v_key_2004_; uint8_t v___x_2005_; 
v_key_2004_ = lean_ctor_get(v___x_2003_, 0);
v___x_2005_ = lean_name_eq(v_x_1997_, v_key_2004_);
return v___x_2005_;
}
case 1:
{
lean_object* v_node_2006_; size_t v___x_2007_; size_t v___x_2008_; 
v_node_2006_ = lean_ctor_get(v___x_2003_, 0);
v___x_2007_ = ((size_t)5ULL);
v___x_2008_ = lean_usize_shift_right(v_x_1996_, v___x_2007_);
v_x_1995_ = v_node_2006_;
v_x_1996_ = v___x_2008_;
goto _start;
}
default: 
{
uint8_t v___x_2010_; 
v___x_2010_ = 0;
return v___x_2010_;
}
}
}
else
{
lean_object* v_ks_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
v_ks_2011_ = lean_ctor_get(v_x_1995_, 0);
v___x_2012_ = lean_unsigned_to_nat(0u);
v___x_2013_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_ks_2011_, v___x_2012_, v_x_1997_);
return v___x_2013_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_2014_, lean_object* v_x_2015_, lean_object* v_x_2016_){
_start:
{
size_t v_x_328__boxed_2017_; uint8_t v_res_2018_; lean_object* v_r_2019_; 
v_x_328__boxed_2017_ = lean_unbox_usize(v_x_2015_);
lean_dec(v_x_2015_);
v_res_2018_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2014_, v_x_328__boxed_2017_, v_x_2016_);
lean_dec(v_x_2016_);
lean_dec_ref(v_x_2014_);
v_r_2019_ = lean_box(v_res_2018_);
return v_r_2019_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object* v_x_2020_, lean_object* v_x_2021_){
_start:
{
uint64_t v___y_2023_; 
if (lean_obj_tag(v_x_2021_) == 0)
{
uint64_t v___x_2026_; 
v___x_2026_ = 1723ULL;
v___y_2023_ = v___x_2026_;
goto v___jp_2022_;
}
else
{
uint64_t v_hash_2027_; 
v_hash_2027_ = lean_ctor_get_uint64(v_x_2021_, sizeof(void*)*2);
v___y_2023_ = v_hash_2027_;
goto v___jp_2022_;
}
v___jp_2022_:
{
size_t v___x_2024_; uint8_t v___x_2025_; 
v___x_2024_ = lean_uint64_to_usize(v___y_2023_);
v___x_2025_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2020_, v___x_2024_, v_x_2021_);
return v___x_2025_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object* v_x_2028_, lean_object* v_x_2029_){
_start:
{
uint8_t v_res_2030_; lean_object* v_r_2031_; 
v_res_2030_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_2028_, v_x_2029_);
lean_dec(v_x_2029_);
lean_dec_ref(v_x_2028_);
v_r_2031_ = lean_box(v_res_2030_);
return v_r_2031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object* v_ext_2032_, lean_object* v_declName_2033_, lean_object* v_a_2034_){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v_ext_2038_; lean_object* v_toEnvExtension_2039_; lean_object* v_env_2040_; lean_object* v_asyncMode_2041_; lean_object* v___x_2042_; lean_object* v_extThms_2043_; uint8_t v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2036_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2037_ = lean_st_ref_get(v_a_2034_);
v_ext_2038_ = lean_ctor_get(v_ext_2032_, 1);
v_toEnvExtension_2039_ = lean_ctor_get(v_ext_2038_, 0);
v_env_2040_ = lean_ctor_get(v___x_2037_, 0);
lean_inc_ref(v_env_2040_);
lean_dec(v___x_2037_);
v_asyncMode_2041_ = lean_ctor_get(v_toEnvExtension_2039_, 2);
v___x_2042_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2036_, v_ext_2032_, v_env_2040_, v_asyncMode_2041_);
v_extThms_2043_ = lean_ctor_get(v___x_2042_, 1);
lean_inc_ref(v_extThms_2043_);
lean_dec(v___x_2042_);
v___x_2044_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_extThms_2043_, v_declName_2033_);
lean_dec_ref(v_extThms_2043_);
v___x_2045_ = lean_box(v___x_2044_);
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object* v_ext_2047_, lean_object* v_declName_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2047_, v_declName_2048_, v_a_2049_);
lean_dec(v_a_2049_);
lean_dec(v_declName_2048_);
lean_dec_ref(v_ext_2047_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object* v_ext_2052_, lean_object* v_declName_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2052_, v_declName_2053_, v_a_2055_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object* v_ext_2058_, lean_object* v_declName_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(v_ext_2058_, v_declName_2059_, v_a_2060_, v_a_2061_);
lean_dec(v_a_2061_);
lean_dec_ref(v_a_2060_);
lean_dec(v_declName_2059_);
lean_dec_ref(v_ext_2058_);
return v_res_2063_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object* v_00_u03b2_2064_, lean_object* v_x_2065_, lean_object* v_x_2066_){
_start:
{
uint8_t v___x_2067_; 
v___x_2067_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_2065_, v_x_2066_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object* v_00_u03b2_2068_, lean_object* v_x_2069_, lean_object* v_x_2070_){
_start:
{
uint8_t v_res_2071_; lean_object* v_r_2072_; 
v_res_2071_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(v_00_u03b2_2068_, v_x_2069_, v_x_2070_);
lean_dec(v_x_2070_);
lean_dec_ref(v_x_2069_);
v_r_2072_ = lean_box(v_res_2071_);
return v_r_2072_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_2073_, lean_object* v_x_2074_, size_t v_x_2075_, lean_object* v_x_2076_){
_start:
{
uint8_t v___x_2077_; 
v___x_2077_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2074_, v_x_2075_, v_x_2076_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2078_, lean_object* v_x_2079_, lean_object* v_x_2080_, lean_object* v_x_2081_){
_start:
{
size_t v_x_413__boxed_2082_; uint8_t v_res_2083_; lean_object* v_r_2084_; 
v_x_413__boxed_2082_ = lean_unbox_usize(v_x_2080_);
lean_dec(v_x_2080_);
v_res_2083_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(v_00_u03b2_2078_, v_x_2079_, v_x_413__boxed_2082_, v_x_2081_);
lean_dec(v_x_2081_);
lean_dec_ref(v_x_2079_);
v_r_2084_ = lean_box(v_res_2083_);
return v_r_2084_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2085_, lean_object* v_keys_2086_, lean_object* v_vals_2087_, lean_object* v_heq_2088_, lean_object* v_i_2089_, lean_object* v_k_2090_){
_start:
{
uint8_t v___x_2091_; 
v___x_2091_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_2086_, v_i_2089_, v_k_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2092_, lean_object* v_keys_2093_, lean_object* v_vals_2094_, lean_object* v_heq_2095_, lean_object* v_i_2096_, lean_object* v_k_2097_){
_start:
{
uint8_t v_res_2098_; lean_object* v_r_2099_; 
v_res_2098_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(v_00_u03b2_2092_, v_keys_2093_, v_vals_2094_, v_heq_2095_, v_i_2096_, v_k_2097_);
lean_dec(v_k_2097_);
lean_dec_ref(v_vals_2094_);
lean_dec_ref(v_keys_2093_);
v_r_2099_ = lean_box(v_res_2098_);
return v_r_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object* v_ext_2100_, lean_object* v_declName_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v_ext_2106_; lean_object* v_toEnvExtension_2107_; lean_object* v_env_2108_; lean_object* v_asyncMode_2109_; lean_object* v___x_2110_; lean_object* v_inj_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2104_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2105_ = lean_st_ref_get(v_a_2102_);
v_ext_2106_ = lean_ctor_get(v_ext_2100_, 1);
v_toEnvExtension_2107_ = lean_ctor_get(v_ext_2106_, 0);
v_env_2108_ = lean_ctor_get(v___x_2105_, 0);
lean_inc_ref(v_env_2108_);
lean_dec(v___x_2105_);
v_asyncMode_2109_ = lean_ctor_get(v_toEnvExtension_2107_, 2);
v___x_2110_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2104_, v_ext_2100_, v_env_2108_, v_asyncMode_2109_);
v_inj_2111_ = lean_ctor_get(v___x_2110_, 4);
lean_inc_ref(v_inj_2111_);
lean_dec(v___x_2110_);
v___x_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2112_, 0, v_declName_2101_);
v___x_2113_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_inj_2111_, v___x_2112_);
lean_dec_ref_known(v___x_2112_, 1);
lean_dec_ref(v_inj_2111_);
v___x_2114_ = lean_box(v___x_2113_);
v___x_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object* v_ext_2116_, lean_object* v_declName_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2116_, v_declName_2117_, v_a_2118_);
lean_dec(v_a_2118_);
lean_dec_ref(v_ext_2116_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object* v_ext_2121_, lean_object* v_declName_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2121_, v_declName_2122_, v_a_2124_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object* v_ext_2127_, lean_object* v_declName_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(v_ext_2127_, v_declName_2128_, v_a_2129_, v_a_2130_);
lean_dec(v_a_2130_);
lean_dec_ref(v_a_2129_);
lean_dec_ref(v_ext_2127_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object* v_ext_2133_, lean_object* v_declName_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v_ext_2139_; lean_object* v_toEnvExtension_2140_; lean_object* v_env_2141_; lean_object* v_asyncMode_2142_; lean_object* v___x_2143_; lean_object* v_funCC_2144_; uint8_t v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2137_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2138_ = lean_st_ref_get(v_a_2135_);
v_ext_2139_ = lean_ctor_get(v_ext_2133_, 1);
v_toEnvExtension_2140_ = lean_ctor_get(v_ext_2139_, 0);
v_env_2141_ = lean_ctor_get(v___x_2138_, 0);
lean_inc_ref(v_env_2141_);
lean_dec(v___x_2138_);
v_asyncMode_2142_ = lean_ctor_get(v_toEnvExtension_2140_, 2);
v___x_2143_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2137_, v_ext_2133_, v_env_2141_, v_asyncMode_2142_);
v_funCC_2144_ = lean_ctor_get(v___x_2143_, 2);
lean_inc(v_funCC_2144_);
lean_dec(v___x_2143_);
v___x_2145_ = l_Lean_NameSet_contains(v_funCC_2144_, v_declName_2134_);
lean_dec(v_funCC_2144_);
v___x_2146_ = lean_box(v___x_2145_);
v___x_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object* v_ext_2148_, lean_object* v_declName_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2148_, v_declName_2149_, v_a_2150_);
lean_dec(v_a_2150_);
lean_dec(v_declName_2149_);
lean_dec_ref(v_ext_2148_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object* v_ext_2153_, lean_object* v_declName_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2153_, v_declName_2154_, v_a_2156_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object* v_ext_2159_, lean_object* v_declName_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(v_ext_2159_, v_declName_2160_, v_a_2161_, v_a_2162_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
lean_dec(v_declName_2160_);
lean_dec_ref(v_ext_2159_);
return v_res_2164_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7));
v___x_2189_ = l_Lean_mkAtom(v___x_2188_);
return v___x_2189_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9);
v___x_2191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2192_ = lean_array_push(v___x_2191_, v___x_2190_);
return v___x_2192_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14));
v___x_2202_ = l_Lean_mkAtom(v___x_2201_);
return v___x_2202_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15);
v___x_2204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2205_ = lean_array_push(v___x_2204_, v___x_2203_);
return v___x_2205_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2206_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16);
v___x_2207_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13));
v___x_2208_ = lean_box(2);
v___x_2209_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
lean_ctor_set(v___x_2209_, 1, v___x_2207_);
lean_ctor_set(v___x_2209_, 2, v___x_2206_);
return v___x_2209_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17);
v___x_2211_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10);
v___x_2212_ = lean_array_push(v___x_2211_, v___x_2210_);
return v___x_2212_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2213_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18);
v___x_2214_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8));
v___x_2215_ = lean_box(2);
v___x_2216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
lean_ctor_set(v___x_2216_, 1, v___x_2214_);
lean_ctor_set(v___x_2216_, 2, v___x_2213_);
return v___x_2216_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2217_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19);
v___x_2218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2219_ = lean_array_push(v___x_2218_, v___x_2217_);
return v___x_2219_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2220_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20);
v___x_2221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6));
v___x_2222_ = lean_box(2);
v___x_2223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
lean_ctor_set(v___x_2223_, 1, v___x_2221_);
lean_ctor_set(v___x_2223_, 2, v___x_2220_);
return v___x_2223_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21);
v___x_2225_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2226_ = lean_array_push(v___x_2225_, v___x_2224_);
return v___x_2226_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2227_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22);
v___x_2228_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4));
v___x_2229_ = lean_box(2);
v___x_2230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
lean_ctor_set(v___x_2230_, 1, v___x_2228_);
lean_ctor_set(v___x_2230_, 2, v___x_2227_);
return v___x_2230_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23);
v___x_2232_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2233_ = lean_array_push(v___x_2232_, v___x_2231_);
return v___x_2233_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2234_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24);
v___x_2235_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1));
v___x_2236_ = lean_box(2);
v___x_2237_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
lean_ctor_set(v___x_2237_, 1, v___x_2235_);
lean_ctor_set(v___x_2237_, 2, v___x_2234_);
return v___x_2237_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1(void){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object* v_declName_2239_, lean_object* v_ext_2240_, lean_object* v_____r_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
uint8_t v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = 0;
lean_inc(v_declName_2239_);
v___x_2248_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_2239_, v___x_2247_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; uint8_t v___x_2250_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_a_2249_);
lean_dec_ref_known(v___x_2248_, 1);
v___x_2250_ = lean_unbox(v_a_2249_);
lean_dec(v_a_2249_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; lean_object* v_a_2252_; uint8_t v___x_2253_; 
v___x_2251_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2240_, v_declName_2239_, v___y_2245_);
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2252_);
lean_dec_ref(v___x_2251_);
v___x_2253_ = lean_unbox(v_a_2252_);
lean_dec(v_a_2252_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; lean_object* v_a_2255_; uint8_t v___x_2256_; 
lean_inc(v_declName_2239_);
v___x_2254_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2240_, v_declName_2239_, v___y_2245_);
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_a_2255_);
lean_dec_ref(v___x_2254_);
v___x_2256_ = lean_unbox(v_a_2255_);
lean_dec(v_a_2255_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; lean_object* v_a_2258_; uint8_t v___x_2259_; 
v___x_2257_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2240_, v_declName_2239_, v___y_2245_);
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref(v___x_2257_);
v___x_2259_ = lean_unbox(v_a_2258_);
lean_dec(v_a_2258_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; 
v___x_2260_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_2240_, v_declName_2239_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
return v___x_2260_;
}
else
{
lean_object* v___x_2261_; 
v___x_2261_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_2240_, v_declName_2239_, v___y_2244_, v___y_2245_);
return v___x_2261_;
}
}
else
{
lean_object* v___x_2262_; 
v___x_2262_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_2240_, v_declName_2239_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
return v___x_2262_;
}
}
else
{
lean_object* v___x_2263_; 
v___x_2263_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_2240_, v_declName_2239_, v___y_2244_, v___y_2245_);
return v___x_2263_;
}
}
else
{
lean_object* v___x_2264_; 
v___x_2264_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_2240_, v_declName_2239_, v___y_2244_, v___y_2245_);
return v___x_2264_;
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
lean_dec_ref(v_ext_2240_);
lean_dec(v_declName_2239_);
v_a_2265_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2248_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2248_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object* v_declName_2273_, lean_object* v_ext_2274_, lean_object* v_____r_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2273_, v_ext_2274_, v_____r_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(lean_object* v_msgData_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v___x_2288_; lean_object* v_env_2289_; lean_object* v___x_2290_; lean_object* v_toCold_2291_; lean_object* v_mctx_2292_; lean_object* v_lctx_2293_; lean_object* v_options_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2288_ = lean_st_ref_get(v___y_2286_);
v_env_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc_ref(v_env_2289_);
lean_dec(v___x_2288_);
v___x_2290_ = lean_st_ref_get(v___y_2284_);
v_toCold_2291_ = lean_ctor_get(v___y_2285_, 0);
v_mctx_2292_ = lean_ctor_get(v___x_2290_, 0);
lean_inc_ref(v_mctx_2292_);
lean_dec(v___x_2290_);
v_lctx_2293_ = lean_ctor_get(v___y_2283_, 2);
v_options_2294_ = lean_ctor_get(v_toCold_2291_, 2);
lean_inc_ref(v_options_2294_);
lean_inc_ref(v_lctx_2293_);
v___x_2295_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2295_, 0, v_env_2289_);
lean_ctor_set(v___x_2295_, 1, v_mctx_2292_);
lean_ctor_set(v___x_2295_, 2, v_lctx_2293_);
lean_ctor_set(v___x_2295_, 3, v_options_2294_);
v___x_2296_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
lean_ctor_set(v___x_2296_, 1, v_msgData_2282_);
v___x_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0___boxed(lean_object* v_msgData_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msgData_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object* v_msg_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_ref_2311_; lean_object* v___x_2312_; lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2321_; 
v_ref_2311_ = lean_ctor_get(v___y_2308_, 2);
v___x_2312_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2321_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2321_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2319_; 
lean_inc(v_ref_2311_);
v___x_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2317_, 0, v_ref_2311_);
lean_ctor_set(v___x_2317_, 1, v_a_2313_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set_tag(v___x_2315_, 1);
lean_ctor_set(v___x_2315_, 0, v___x_2317_);
v___x_2319_ = v___x_2315_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object* v_msg_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
return v_res_2328_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2335_; uint64_t v___x_2336_; 
v___x_2335_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2336_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2335_);
return v___x_2336_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2337_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1);
v___x_2338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2339_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2339_, 0, v___x_2338_);
lean_ctor_set_uint64(v___x_2339_, sizeof(void*)*1, v___x_2337_);
return v___x_2339_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
return v___x_2341_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2342_ = lean_box(1);
v___x_2343_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2344_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
lean_ctor_set(v___x_2345_, 1, v___x_2343_);
lean_ctor_set(v___x_2345_, 2, v___x_2342_);
return v___x_2345_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2348_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2349_ = lean_unsigned_to_nat(0u);
v___x_2350_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
lean_ctor_set(v___x_2350_, 2, v___x_2349_);
lean_ctor_set(v___x_2350_, 3, v___x_2349_);
lean_ctor_set(v___x_2350_, 4, v___x_2348_);
lean_ctor_set(v___x_2350_, 5, v___x_2348_);
lean_ctor_set(v___x_2350_, 6, v___x_2348_);
lean_ctor_set(v___x_2350_, 7, v___x_2348_);
lean_ctor_set(v___x_2350_, 8, v___x_2348_);
lean_ctor_set(v___x_2350_, 9, v___x_2348_);
lean_ctor_set(v___x_2350_, 10, v___x_2348_);
return v___x_2350_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2352_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
lean_ctor_set(v___x_2352_, 2, v___x_2351_);
lean_ctor_set(v___x_2352_, 3, v___x_2351_);
lean_ctor_set(v___x_2352_, 4, v___x_2351_);
lean_ctor_set(v___x_2352_, 5, v___x_2351_);
return v___x_2352_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
lean_ctor_set(v___x_2354_, 1, v___x_2353_);
lean_ctor_set(v___x_2354_, 2, v___x_2353_);
lean_ctor_set(v___x_2354_, 3, v___x_2353_);
lean_ctor_set(v___x_2354_, 4, v___x_2353_);
return v___x_2354_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10(void){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2356_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9));
v___x_2357_ = l_Lean_stringToMessageData(v___x_2356_);
return v___x_2357_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12(void){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11));
v___x_2360_ = l_Lean_stringToMessageData(v___x_2359_);
return v___x_2360_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14(void){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13));
v___x_2363_ = l_Lean_stringToMessageData(v___x_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object* v_ext_2364_, lean_object* v___x_2365_, uint8_t v_showInfo_2366_, lean_object* v_attrName_2367_, lean_object* v_declName_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
uint8_t v___x_2372_; uint8_t v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___y_2387_; 
v___x_2372_ = 1;
v___x_2373_ = 0;
v___x_2374_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_2375_ = lean_unsigned_to_nat(0u);
v___x_2376_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2377_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2378_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5));
v___x_2379_ = lean_box(0);
lean_inc(v___x_2365_);
v___x_2380_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2380_, 0, v___x_2374_);
lean_ctor_set(v___x_2380_, 1, v___x_2365_);
lean_ctor_set(v___x_2380_, 2, v___x_2377_);
lean_ctor_set(v___x_2380_, 3, v___x_2378_);
lean_ctor_set(v___x_2380_, 4, v___x_2379_);
lean_ctor_set(v___x_2380_, 5, v___x_2375_);
lean_ctor_set(v___x_2380_, 6, v___x_2379_);
lean_ctor_set_uint8(v___x_2380_, sizeof(void*)*7, v___x_2373_);
lean_ctor_set_uint8(v___x_2380_, sizeof(void*)*7 + 1, v___x_2373_);
lean_ctor_set_uint8(v___x_2380_, sizeof(void*)*7 + 2, v___x_2373_);
lean_ctor_set_uint8(v___x_2380_, sizeof(void*)*7 + 3, v___x_2372_);
v___x_2381_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6);
v___x_2382_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_2383_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_2384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2381_);
lean_ctor_set(v___x_2384_, 1, v___x_2382_);
lean_ctor_set(v___x_2384_, 2, v___x_2365_);
lean_ctor_set(v___x_2384_, 3, v___x_2376_);
lean_ctor_set(v___x_2384_, 4, v___x_2383_);
v___x_2385_ = lean_st_mk_ref(v___x_2384_);
if (v_showInfo_2366_ == 0)
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
lean_dec(v_attrName_2367_);
v___x_2397_ = lean_box(0);
v___x_2398_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2368_, v_ext_2364_, v___x_2397_, v___x_2380_, v___x_2385_, v___y_2369_, v___y_2370_);
lean_dec_ref_known(v___x_2380_, 7);
v___y_2387_ = v___x_2398_;
goto v___jp_2386_;
}
else
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
lean_dec(v_declName_2368_);
lean_dec_ref(v_ext_2364_);
v___x_2399_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10);
v___x_2400_ = l_Lean_MessageData_ofName(v_attrName_2367_);
lean_inc_ref(v___x_2400_);
v___x_2401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2399_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
v___x_2402_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12);
v___x_2403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2401_);
lean_ctor_set(v___x_2403_, 1, v___x_2402_);
v___x_2404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
lean_ctor_set(v___x_2404_, 1, v___x_2400_);
v___x_2405_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14);
v___x_2406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2404_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2406_, v___x_2380_, v___x_2385_, v___y_2369_, v___y_2370_);
lean_dec_ref_known(v___x_2380_, 7);
v___y_2387_ = v___x_2407_;
goto v___jp_2386_;
}
v___jp_2386_:
{
if (lean_obj_tag(v___y_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2396_; 
v_a_2388_ = lean_ctor_get(v___y_2387_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___y_2387_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2390_ = v___y_2387_;
v_isShared_2391_ = v_isSharedCheck_2396_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___y_2387_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2396_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; lean_object* v___x_2394_; 
v___x_2392_ = lean_st_ref_get(v___x_2385_);
lean_dec(v___x_2385_);
lean_dec(v___x_2392_);
if (v_isShared_2391_ == 0)
{
v___x_2394_ = v___x_2390_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2388_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
else
{
lean_dec(v___x_2385_);
return v___y_2387_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object* v_ext_2408_, lean_object* v___x_2409_, lean_object* v_showInfo_2410_, lean_object* v_attrName_2411_, lean_object* v_declName_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
uint8_t v_showInfo_boxed_2416_; lean_object* v_res_2417_; 
v_showInfo_boxed_2416_ = lean_unbox(v_showInfo_2410_);
v_res_2417_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(v_ext_2408_, v___x_2409_, v_showInfo_boxed_2416_, v_attrName_2411_, v_declName_2412_, v___y_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object* v_ext_2420_, uint8_t v_attrKind_2421_, uint8_t v_showInfo_2422_, uint8_t v_minIndexable_2423_, lean_object* v_as_x27_2424_, lean_object* v_b_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
if (lean_obj_tag(v_as_x27_2424_) == 0)
{
lean_object* v___x_2431_; 
lean_dec_ref(v_ext_2420_);
v___x_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2431_, 0, v_b_2425_);
return v___x_2431_;
}
else
{
lean_object* v_head_2432_; lean_object* v_tail_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v_head_2432_ = lean_ctor_get(v_as_x27_2424_, 0);
v_tail_2433_ = lean_ctor_get(v_as_x27_2424_, 1);
v___x_2434_ = lean_box(0);
v___x_2435_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2429_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
v___x_2437_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0));
lean_inc(v_head_2432_);
lean_inc_ref(v_ext_2420_);
v___x_2438_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2420_, v_head_2432_, v_attrKind_2421_, v___x_2437_, v_a_2436_, v_showInfo_2422_, v_minIndexable_2423_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_dec_ref_known(v___x_2438_, 1);
v_as_x27_2424_ = v_tail_2433_;
v_b_2425_ = v___x_2434_;
goto _start;
}
else
{
lean_dec_ref(v_ext_2420_);
return v___x_2438_;
}
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_dec_ref(v_ext_2420_);
v_a_2440_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2435_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2435_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object* v_ext_2448_, lean_object* v_attrKind_2449_, lean_object* v_showInfo_2450_, lean_object* v_minIndexable_2451_, lean_object* v_as_x27_2452_, lean_object* v_b_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
uint8_t v_attrKind_boxed_2459_; uint8_t v_showInfo_boxed_2460_; uint8_t v_minIndexable_boxed_2461_; lean_object* v_res_2462_; 
v_attrKind_boxed_2459_ = lean_unbox(v_attrKind_2449_);
v_showInfo_boxed_2460_ = lean_unbox(v_showInfo_2450_);
v_minIndexable_boxed_2461_ = lean_unbox(v_minIndexable_2451_);
v_res_2462_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2448_, v_attrKind_boxed_2459_, v_showInfo_boxed_2460_, v_minIndexable_boxed_2461_, v_as_x27_2452_, v_b_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v_as_x27_2452_);
return v_res_2462_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0));
v___x_2465_ = l_Lean_stringToMessageData(v___x_2464_);
return v___x_2465_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2));
v___x_2468_ = l_Lean_stringToMessageData(v___x_2467_);
return v___x_2468_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5(void){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4));
v___x_2471_ = l_Lean_stringToMessageData(v___x_2470_);
return v___x_2471_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6));
v___x_2474_ = l_Lean_stringToMessageData(v___x_2473_);
return v___x_2474_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10));
v___x_2480_ = l_Lean_stringToMessageData(v___x_2479_);
return v___x_2480_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13(void){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12));
v___x_2483_ = l_Lean_stringToMessageData(v___x_2482_);
return v___x_2483_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15(void){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14));
v___x_2486_ = l_Lean_stringToMessageData(v___x_2485_);
return v___x_2486_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17(void){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__16));
v___x_2489_ = l_Lean_stringToMessageData(v___x_2488_);
return v___x_2489_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19(void){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__18));
v___x_2492_ = l_Lean_stringToMessageData(v___x_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object* v_declName_2493_, uint8_t v___x_2494_, uint8_t v_attrKind_2495_, lean_object* v_stx_2496_, lean_object* v_ext_2497_, uint8_t v_showInfo_2498_, uint8_t v_minIndexable_2499_, lean_object* v_attrName_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_2496_, v___y_2503_, v___y_2504_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2531_);
lean_dec_ref_known(v___x_2530_, 1);
switch(lean_obj_tag(v_a_2531_))
{
case 0:
{
lean_object* v_k_2532_; 
lean_dec(v_attrName_2500_);
lean_dec(v_stx_2496_);
v_k_2532_ = lean_ctor_get(v_a_2531_, 0);
lean_inc(v_k_2532_);
lean_dec_ref_known(v_a_2531_, 1);
if (lean_obj_tag(v_k_2532_) == 9)
{
lean_object* v___x_2533_; 
lean_dec_ref(v_ext_2497_);
lean_dec(v_declName_2493_);
v___x_2533_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___y_2503_, v___y_2504_);
return v___x_2533_;
}
else
{
lean_object* v___x_2534_; 
v___x_2534_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2504_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; lean_object* v___x_2536_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_a_2535_);
lean_dec_ref_known(v___x_2534_, 1);
v___x_2536_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2497_, v_declName_2493_, v_attrKind_2495_, v_k_2532_, v_a_2535_, v_showInfo_2498_, v_minIndexable_2499_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
return v___x_2536_;
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec(v_k_2532_);
lean_dec_ref(v_ext_2497_);
lean_dec(v_declName_2493_);
v_a_2537_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2534_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2534_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
case 1:
{
uint8_t v_eager_2545_; lean_object* v___x_2546_; 
lean_dec(v_attrName_2500_);
lean_dec(v_stx_2496_);
v_eager_2545_ = lean_ctor_get_uint8(v_a_2531_, 0);
lean_dec_ref_known(v_a_2531_, 0);
v___x_2546_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2497_, v_declName_2493_, v_eager_2545_, v_attrKind_2495_, v___y_2503_, v___y_2504_);
return v___x_2546_;
}
case 2:
{
lean_object* v___x_2547_; 
lean_dec(v_stx_2496_);
lean_inc(v_declName_2493_);
v___x_2547_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_2493_, v___x_2494_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref_known(v___x_2547_, 1);
if (lean_obj_tag(v_a_2548_) == 1)
{
lean_object* v_val_2549_; lean_object* v_ctors_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
lean_dec(v_attrName_2500_);
lean_dec(v_declName_2493_);
v_val_2549_ = lean_ctor_get(v_a_2548_, 0);
lean_inc(v_val_2549_);
lean_dec_ref_known(v_a_2548_, 1);
v_ctors_2550_ = lean_ctor_get(v_val_2549_, 4);
lean_inc(v_ctors_2550_);
lean_dec(v_val_2549_);
v___x_2551_ = lean_box(0);
v___x_2552_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2497_, v_attrKind_2495_, v_showInfo_2498_, v_minIndexable_2499_, v_ctors_2550_, v___x_2551_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
lean_dec(v_ctors_2550_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; 
v_unused_2560_ = lean_ctor_get(v___x_2552_, 0);
lean_dec(v_unused_2560_);
v___x_2554_ = v___x_2552_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_dec(v___x_2552_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v___x_2551_);
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2551_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
else
{
return v___x_2552_;
}
}
else
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
lean_dec(v_a_2548_);
lean_dec_ref(v_ext_2497_);
v___x_2561_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3);
v___x_2562_ = l_Lean_MessageData_ofName(v_attrName_2500_);
v___x_2563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2561_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5);
v___x_2565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2563_);
lean_ctor_set(v___x_2565_, 1, v___x_2564_);
v___x_2566_ = l_Lean_MessageData_ofConstName(v_declName_2493_, v___x_2494_);
v___x_2567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2565_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7);
v___x_2569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2567_);
lean_ctor_set(v___x_2569_, 1, v___x_2568_);
v___x_2570_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2569_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
return v___x_2570_;
}
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
lean_dec(v_attrName_2500_);
lean_dec_ref(v_ext_2497_);
lean_dec(v_declName_2493_);
v_a_2571_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v___x_2547_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2547_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
case 3:
{
lean_object* v___x_2579_; 
lean_dec(v_attrName_2500_);
lean_inc(v_declName_2493_);
v___x_2579_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_2493_, v___x_2494_, v___y_2503_, v___y_2504_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref_known(v___x_2579_, 1);
if (lean_obj_tag(v_a_2580_) == 1)
{
lean_object* v_val_2581_; lean_object* v___x_2582_; 
lean_dec(v_stx_2496_);
lean_dec(v_declName_2493_);
v_val_2581_ = lean_ctor_get(v_a_2580_, 0);
lean_inc_n(v_val_2581_, 2);
lean_dec_ref_known(v_a_2580_, 1);
lean_inc_ref(v_ext_2497_);
v___x_2582_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2497_, v_val_2581_, v___x_2494_, v_attrKind_2495_, v___y_2503_, v___y_2504_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v___x_2583_; 
lean_dec_ref_known(v___x_2582_, 1);
v___x_2583_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_2581_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2604_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2586_ = v___x_2583_;
v_isShared_2587_ = v_isSharedCheck_2604_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2583_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2604_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
if (lean_obj_tag(v_a_2584_) == 1)
{
lean_object* v_val_2588_; lean_object* v_ctors_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
lean_del_object(v___x_2586_);
v_val_2588_ = lean_ctor_get(v_a_2584_, 0);
lean_inc(v_val_2588_);
lean_dec_ref_known(v_a_2584_, 1);
v_ctors_2589_ = lean_ctor_get(v_val_2588_, 4);
lean_inc(v_ctors_2589_);
lean_dec(v_val_2588_);
v___x_2590_ = lean_box(0);
v___x_2591_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2497_, v_attrKind_2495_, v_showInfo_2498_, v_minIndexable_2499_, v_ctors_2589_, v___x_2590_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
lean_dec(v_ctors_2589_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2598_ == 0)
{
lean_object* v_unused_2599_; 
v_unused_2599_ = lean_ctor_get(v___x_2591_, 0);
lean_dec(v_unused_2599_);
v___x_2593_ = v___x_2591_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_dec(v___x_2591_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 0, v___x_2590_);
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2590_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
else
{
return v___x_2591_;
}
}
else
{
lean_object* v___x_2600_; lean_object* v___x_2602_; 
lean_dec(v_a_2584_);
lean_dec_ref(v_ext_2497_);
v___x_2600_ = lean_box(0);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 0, v___x_2600_);
v___x_2602_ = v___x_2586_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec_ref(v_ext_2497_);
v_a_2605_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2583_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2583_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
else
{
lean_dec(v_val_2581_);
lean_dec_ref(v_ext_2497_);
return v___x_2582_;
}
}
else
{
lean_object* v___x_2613_; 
lean_dec(v_a_2580_);
v___x_2613_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2504_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v___x_2615_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_a_2614_);
lean_dec_ref_known(v___x_2613_, 1);
v___x_2615_ = l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(v_ext_2497_, v_stx_2496_, v_declName_2493_, v_attrKind_2495_, v_a_2614_, v_minIndexable_2499_, v_showInfo_2498_, v___x_2494_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
return v___x_2615_;
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec_ref(v_ext_2497_);
lean_dec(v_stx_2496_);
lean_dec(v_declName_2493_);
v_a_2616_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2613_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2613_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec_ref(v_ext_2497_);
lean_dec(v_stx_2496_);
lean_dec(v_declName_2493_);
v_a_2624_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2579_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2579_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
case 4:
{
lean_object* v___x_2632_; 
lean_dec(v_attrName_2500_);
lean_dec(v_stx_2496_);
v___x_2632_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_2497_, v_declName_2493_, v_attrKind_2495_, v___y_2503_, v___y_2504_);
return v___x_2632_;
}
case 5:
{
lean_object* v_prio_2633_; lean_object* v___x_2634_; uint8_t v___x_2635_; 
lean_dec_ref(v_ext_2497_);
lean_dec(v_stx_2496_);
v_prio_2633_ = lean_ctor_get(v_a_2531_, 0);
lean_inc(v_prio_2633_);
lean_dec_ref_known(v_a_2531_, 1);
v___x_2634_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2635_ = lean_name_eq(v_attrName_2500_, v___x_2634_);
lean_dec(v_attrName_2500_);
if (v___x_2635_ == 0)
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
lean_dec(v_prio_2633_);
lean_dec(v_declName_2493_);
v___x_2636_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11);
v___x_2637_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2636_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
return v___x_2637_;
}
else
{
lean_object* v___x_2638_; 
v___x_2638_ = l_Lean_Meta_Grind_addSymbolPriorityAttr(v_declName_2493_, v_attrKind_2495_, v_prio_2633_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
return v___x_2638_;
}
}
case 6:
{
lean_object* v___x_2639_; 
lean_dec(v_attrName_2500_);
lean_dec(v_stx_2496_);
v___x_2639_ = l_Lean_Meta_Grind_Extension_addInjectiveAttr(v_ext_2497_, v_declName_2493_, v_attrKind_2495_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
return v___x_2639_;
}
case 7:
{
lean_object* v___x_2640_; 
lean_dec(v_attrName_2500_);
lean_dec(v_stx_2496_);
v___x_2640_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_2497_, v_declName_2493_, v_attrKind_2495_, v___y_2503_, v___y_2504_);
return v___x_2640_;
}
case 8:
{
uint8_t v_post_2641_; uint8_t v_inv_2642_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
lean_dec_ref(v_ext_2497_);
lean_dec(v_stx_2496_);
v_post_2641_ = lean_ctor_get_uint8(v_a_2531_, 0);
v_inv_2642_ = lean_ctor_get_uint8(v_a_2531_, 1);
lean_dec_ref_known(v_a_2531_, 0);
v___x_2651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2652_ = lean_name_eq(v_attrName_2500_, v___x_2651_);
lean_dec(v_attrName_2500_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_dec(v_declName_2493_);
v___x_2653_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13);
v___x_2654_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2653_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
return v___x_2654_;
}
else
{
v___y_2644_ = v___y_2501_;
v___y_2645_ = v___y_2502_;
v___y_2646_ = v___y_2503_;
v___y_2647_ = v___y_2504_;
goto v___jp_2643_;
}
v___jp_2643_:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2648_ = l_Lean_Meta_Grind_normExt;
v___x_2649_ = lean_unsigned_to_nat(1000u);
v___x_2650_ = l_Lean_Meta_addSimpTheorem(v___x_2648_, v_declName_2493_, v_post_2641_, v_inv_2642_, v_attrKind_2495_, v___x_2649_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
return v___x_2650_;
}
}
case 9:
{
lean_object* v___x_2655_; uint8_t v___x_2656_; 
lean_dec_ref(v_ext_2497_);
lean_dec(v_stx_2496_);
v___x_2655_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2656_ = lean_name_eq(v_attrName_2500_, v___x_2655_);
lean_dec(v_attrName_2500_);
if (v___x_2656_ == 0)
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
lean_dec(v_declName_2493_);
v___x_2657_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15);
v___x_2658_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2657_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
return v___x_2658_;
}
else
{
goto v___jp_2506_;
}
}
case 10:
{
uint8_t v_fallback_2659_; lean_object* v___x_2660_; uint8_t v___x_2661_; 
lean_dec_ref(v_ext_2497_);
lean_dec(v_stx_2496_);
v_fallback_2659_ = lean_ctor_get_uint8(v_a_2531_, 0);
lean_dec_ref_known(v_a_2531_, 0);
v___x_2660_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2661_ = lean_name_eq(v_attrName_2500_, v___x_2660_);
lean_dec(v_attrName_2500_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
lean_dec(v_declName_2493_);
v___x_2662_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__17);
v___x_2663_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2662_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
return v___x_2663_;
}
else
{
lean_object* v___x_2664_; 
v___x_2664_ = l_Lean_Meta_Grind_addHomoAttr(v_declName_2493_, v_attrKind_2495_, v_fallback_2659_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
return v___x_2664_;
}
}
default: 
{
lean_object* v___x_2665_; uint8_t v___x_2666_; 
lean_dec_ref(v_ext_2497_);
lean_dec(v_stx_2496_);
v___x_2665_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2666_ = lean_name_eq(v_attrName_2500_, v___x_2665_);
lean_dec(v_attrName_2500_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
lean_dec(v_declName_2493_);
v___x_2667_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__19);
v___x_2668_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2667_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
return v___x_2668_;
}
else
{
lean_object* v___x_2669_; 
v___x_2669_ = l_Lean_Meta_Grind_addHomoPredAttr(v_declName_2493_, v_attrKind_2495_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
return v___x_2669_;
}
}
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
lean_dec(v_attrName_2500_);
lean_dec_ref(v_ext_2497_);
lean_dec(v_stx_2496_);
lean_dec(v_declName_2493_);
v_a_2670_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2530_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2530_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
v___jp_2506_:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2507_ = l_Lean_Meta_Grind_normExt;
v___x_2508_ = lean_unsigned_to_nat(1000u);
v___x_2509_ = l_Lean_Meta_addDeclToUnfold(v___x_2507_, v_declName_2493_, v___x_2494_, v___x_2494_, v___x_2508_, v_attrKind_2495_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2521_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2512_ = v___x_2509_;
v_isShared_2513_ = v_isSharedCheck_2521_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2509_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2521_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
uint8_t v___x_2514_; 
v___x_2514_ = lean_unbox(v_a_2510_);
lean_dec(v_a_2510_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
lean_del_object(v___x_2512_);
v___x_2515_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1);
v___x_2516_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2515_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
return v___x_2516_;
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2517_ = lean_box(0);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v___x_2517_);
v___x_2519_ = v___x_2512_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2517_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
v_a_2522_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2509_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2509_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object* v_declName_2678_, lean_object* v___x_2679_, lean_object* v_attrKind_2680_, lean_object* v_stx_2681_, lean_object* v_ext_2682_, lean_object* v_showInfo_2683_, lean_object* v_minIndexable_2684_, lean_object* v_attrName_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
uint8_t v___x_15181__boxed_2691_; uint8_t v_attrKind_boxed_2692_; uint8_t v_showInfo_boxed_2693_; uint8_t v_minIndexable_boxed_2694_; lean_object* v_res_2695_; 
v___x_15181__boxed_2691_ = lean_unbox(v___x_2679_);
v_attrKind_boxed_2692_ = lean_unbox(v_attrKind_2680_);
v_showInfo_boxed_2693_ = lean_unbox(v_showInfo_2683_);
v_minIndexable_boxed_2694_ = lean_unbox(v_minIndexable_2684_);
v_res_2695_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(v_declName_2678_, v___x_15181__boxed_2691_, v_attrKind_boxed_2692_, v_stx_2681_, v_ext_2682_, v_showInfo_boxed_2693_, v_minIndexable_boxed_2694_, v_attrName_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
return v_res_2695_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2696_; double v___x_2697_; 
v___x_2696_ = lean_unsigned_to_nat(0u);
v___x_2697_ = lean_float_of_nat(v___x_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(lean_object* v_cls_2701_, lean_object* v_msg_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_ref_2708_; lean_object* v___x_2709_; lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2755_; 
v_ref_2708_ = lean_ctor_get(v___y_2705_, 2);
v___x_2709_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2712_ = v___x_2709_;
v_isShared_2713_ = v_isSharedCheck_2755_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2709_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2755_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2714_; lean_object* v_traceState_2715_; lean_object* v_env_2716_; lean_object* v_nextMacroScope_2717_; lean_object* v_ngen_2718_; lean_object* v_auxDeclNGen_2719_; lean_object* v_cache_2720_; lean_object* v_recordedDeps_2721_; lean_object* v_messages_2722_; lean_object* v_infoState_2723_; lean_object* v_snapshotTasks_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2754_; 
v___x_2714_ = lean_st_ref_take(v___y_2706_);
v_traceState_2715_ = lean_ctor_get(v___x_2714_, 4);
v_env_2716_ = lean_ctor_get(v___x_2714_, 0);
v_nextMacroScope_2717_ = lean_ctor_get(v___x_2714_, 1);
v_ngen_2718_ = lean_ctor_get(v___x_2714_, 2);
v_auxDeclNGen_2719_ = lean_ctor_get(v___x_2714_, 3);
v_cache_2720_ = lean_ctor_get(v___x_2714_, 5);
v_recordedDeps_2721_ = lean_ctor_get(v___x_2714_, 6);
v_messages_2722_ = lean_ctor_get(v___x_2714_, 7);
v_infoState_2723_ = lean_ctor_get(v___x_2714_, 8);
v_snapshotTasks_2724_ = lean_ctor_get(v___x_2714_, 9);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2726_ = v___x_2714_;
v_isShared_2727_ = v_isSharedCheck_2754_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_snapshotTasks_2724_);
lean_inc(v_infoState_2723_);
lean_inc(v_messages_2722_);
lean_inc(v_recordedDeps_2721_);
lean_inc(v_cache_2720_);
lean_inc(v_traceState_2715_);
lean_inc(v_auxDeclNGen_2719_);
lean_inc(v_ngen_2718_);
lean_inc(v_nextMacroScope_2717_);
lean_inc(v_env_2716_);
lean_dec(v___x_2714_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2754_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
uint64_t v_tid_2728_; lean_object* v_traces_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2753_; 
v_tid_2728_ = lean_ctor_get_uint64(v_traceState_2715_, sizeof(void*)*1);
v_traces_2729_ = lean_ctor_get(v_traceState_2715_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v_traceState_2715_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2731_ = v_traceState_2715_;
v_isShared_2732_ = v_isSharedCheck_2753_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_traces_2729_);
lean_dec(v_traceState_2715_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2753_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; double v___x_2735_; uint8_t v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2744_; 
v___x_2733_ = lean_box(0);
v___x_2734_ = lean_box(0);
v___x_2735_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_2736_ = 0;
v___x_2737_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2738_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2738_, 0, v_cls_2701_);
lean_ctor_set(v___x_2738_, 1, v___x_2734_);
lean_ctor_set(v___x_2738_, 2, v___x_2737_);
lean_ctor_set_float(v___x_2738_, sizeof(void*)*3, v___x_2735_);
lean_ctor_set_float(v___x_2738_, sizeof(void*)*3 + 8, v___x_2735_);
lean_ctor_set_uint8(v___x_2738_, sizeof(void*)*3 + 16, v___x_2736_);
v___x_2739_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_2740_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2738_);
lean_ctor_set(v___x_2740_, 1, v_a_2710_);
lean_ctor_set(v___x_2740_, 2, v___x_2739_);
lean_inc(v_ref_2708_);
v___x_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2741_, 0, v_ref_2708_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v___x_2742_ = l_Lean_PersistentArray_push___redArg(v_traces_2729_, v___x_2741_);
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 0, v___x_2742_);
v___x_2744_ = v___x_2731_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2742_);
lean_ctor_set_uint64(v_reuseFailAlloc_2752_, sizeof(void*)*1, v_tid_2728_);
v___x_2744_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
lean_object* v___x_2746_; 
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 4, v___x_2744_);
v___x_2746_ = v___x_2726_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_env_2716_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v_nextMacroScope_2717_);
lean_ctor_set(v_reuseFailAlloc_2751_, 2, v_ngen_2718_);
lean_ctor_set(v_reuseFailAlloc_2751_, 3, v_auxDeclNGen_2719_);
lean_ctor_set(v_reuseFailAlloc_2751_, 4, v___x_2744_);
lean_ctor_set(v_reuseFailAlloc_2751_, 5, v_cache_2720_);
lean_ctor_set(v_reuseFailAlloc_2751_, 6, v_recordedDeps_2721_);
lean_ctor_set(v_reuseFailAlloc_2751_, 7, v_messages_2722_);
lean_ctor_set(v_reuseFailAlloc_2751_, 8, v_infoState_2723_);
lean_ctor_set(v_reuseFailAlloc_2751_, 9, v_snapshotTasks_2724_);
v___x_2746_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
lean_object* v___x_2747_; lean_object* v___x_2749_; 
v___x_2747_ = lean_st_ref_put(v___y_2706_, v___x_2746_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v___x_2733_);
v___x_2749_ = v___x_2712_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2733_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___boxed(lean_object* v_cls_2756_, lean_object* v_msg_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2756_, v_msg_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
return v_res_2763_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(lean_object* v_keys_2764_, lean_object* v_i_2765_, lean_object* v_k_2766_){
_start:
{
lean_object* v___x_2767_; uint8_t v___x_2768_; 
v___x_2767_ = lean_array_get_size(v_keys_2764_);
v___x_2768_ = lean_nat_dec_lt(v_i_2765_, v___x_2767_);
if (v___x_2768_ == 0)
{
lean_dec(v_i_2765_);
return v___x_2768_;
}
else
{
lean_object* v_k_x27_2769_; uint8_t v___x_2770_; 
v_k_x27_2769_ = lean_array_fget_borrowed(v_keys_2764_, v_i_2765_);
v___x_2770_ = l_Lean_instBEqExtraModUse_beq(v_k_2766_, v_k_x27_2769_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = lean_unsigned_to_nat(1u);
v___x_2772_ = lean_nat_add(v_i_2765_, v___x_2771_);
lean_dec(v_i_2765_);
v_i_2765_ = v___x_2772_;
goto _start;
}
else
{
lean_dec(v_i_2765_);
return v___x_2768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_keys_2774_, lean_object* v_i_2775_, lean_object* v_k_2776_){
_start:
{
uint8_t v_res_2777_; lean_object* v_r_2778_; 
v_res_2777_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_2774_, v_i_2775_, v_k_2776_);
lean_dec_ref(v_k_2776_);
lean_dec_ref(v_keys_2774_);
v_r_2778_ = lean_box(v_res_2777_);
return v_r_2778_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_x_2779_, size_t v_x_2780_, lean_object* v_x_2781_){
_start:
{
if (lean_obj_tag(v_x_2779_) == 0)
{
lean_object* v_es_2782_; lean_object* v___x_2783_; size_t v___x_2784_; size_t v___x_2785_; lean_object* v_j_2786_; lean_object* v___x_2787_; 
v_es_2782_ = lean_ctor_get(v_x_2779_, 0);
v___x_2783_ = lean_box(2);
v___x_2784_ = ((size_t)31ULL);
v___x_2785_ = lean_usize_land(v_x_2780_, v___x_2784_);
v_j_2786_ = lean_usize_to_nat(v___x_2785_);
v___x_2787_ = lean_array_get_borrowed(v___x_2783_, v_es_2782_, v_j_2786_);
lean_dec(v_j_2786_);
switch(lean_obj_tag(v___x_2787_))
{
case 0:
{
lean_object* v_key_2788_; uint8_t v___x_2789_; 
v_key_2788_ = lean_ctor_get(v___x_2787_, 0);
v___x_2789_ = l_Lean_instBEqExtraModUse_beq(v_x_2781_, v_key_2788_);
return v___x_2789_;
}
case 1:
{
lean_object* v_node_2790_; size_t v___x_2791_; size_t v___x_2792_; 
v_node_2790_ = lean_ctor_get(v___x_2787_, 0);
v___x_2791_ = ((size_t)5ULL);
v___x_2792_ = lean_usize_shift_right(v_x_2780_, v___x_2791_);
v_x_2779_ = v_node_2790_;
v_x_2780_ = v___x_2792_;
goto _start;
}
default: 
{
uint8_t v___x_2794_; 
v___x_2794_ = 0;
return v___x_2794_;
}
}
}
else
{
lean_object* v_ks_2795_; lean_object* v___x_2796_; uint8_t v___x_2797_; 
v_ks_2795_ = lean_ctor_get(v_x_2779_, 0);
v___x_2796_ = lean_unsigned_to_nat(0u);
v___x_2797_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_ks_2795_, v___x_2796_, v_x_2781_);
return v___x_2797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_x_2798_, lean_object* v_x_2799_, lean_object* v_x_2800_){
_start:
{
size_t v_x_15699__boxed_2801_; uint8_t v_res_2802_; lean_object* v_r_2803_; 
v_x_15699__boxed_2801_ = lean_unbox_usize(v_x_2799_);
lean_dec(v_x_2799_);
v_res_2802_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2798_, v_x_15699__boxed_2801_, v_x_2800_);
lean_dec_ref(v_x_2800_);
lean_dec_ref(v_x_2798_);
v_r_2803_ = lean_box(v_res_2802_);
return v_r_2803_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(lean_object* v_x_2804_, lean_object* v_x_2805_){
_start:
{
uint64_t v___x_2806_; size_t v___x_2807_; uint8_t v___x_2808_; 
v___x_2806_ = l_Lean_instHashableExtraModUse_hash(v_x_2805_);
v___x_2807_ = lean_uint64_to_usize(v___x_2806_);
v___x_2808_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2804_, v___x_2807_, v_x_2805_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_2809_, lean_object* v_x_2810_){
_start:
{
uint8_t v_res_2811_; lean_object* v_r_2812_; 
v_res_2811_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_2809_, v_x_2810_);
lean_dec_ref(v_x_2810_);
lean_dec_ref(v_x_2809_);
v_r_2812_ = lean_box(v_res_2811_);
return v_r_2812_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2813_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4(void){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3));
v___x_2819_ = l_Lean_stringToMessageData(v___x_2818_);
return v___x_2819_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2821_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5));
v___x_2822_ = l_Lean_stringToMessageData(v___x_2821_);
return v___x_2822_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2824_ = l_Lean_stringToMessageData(v___x_2823_);
return v___x_2824_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10(void){
_start:
{
lean_object* v_cls_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v_cls_2828_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2));
v___x_2829_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9));
v___x_2830_ = l_Lean_Name_append(v___x_2829_, v_cls_2828_);
return v___x_2830_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11));
v___x_2833_ = l_Lean_stringToMessageData(v___x_2832_);
return v___x_2833_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13));
v___x_2836_ = l_Lean_stringToMessageData(v___x_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object* v_mod_2841_, uint8_t v_isMeta_2842_, lean_object* v_hint_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v_env_2851_; uint8_t v_isExporting_2852_; lean_object* v_entry_2853_; lean_object* v___x_2854_; lean_object* v_env_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___x_2902_; uint8_t v___x_2903_; 
v___x_2849_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0);
v___x_2850_ = lean_st_ref_get(v___y_2847_);
v_env_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc_ref(v_env_2851_);
lean_dec(v___x_2850_);
v_isExporting_2852_ = lean_ctor_get_uint8(v_env_2851_, sizeof(void*)*8);
lean_dec_ref(v_env_2851_);
lean_inc(v_mod_2841_);
v_entry_2853_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2853_, 0, v_mod_2841_);
lean_ctor_set_uint8(v_entry_2853_, sizeof(void*)*1, v_isExporting_2852_);
lean_ctor_set_uint8(v_entry_2853_, sizeof(void*)*1 + 1, v_isMeta_2842_);
v___x_2854_ = lean_st_ref_get(v___y_2847_);
v_env_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc_ref(v_env_2855_);
lean_dec(v___x_2854_);
v___x_2856_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2857_ = lean_box(1);
v___x_2858_ = lean_box(0);
v___x_2902_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2849_, v___x_2856_, v_env_2855_, v___x_2857_, v___x_2858_);
v___x_2903_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_2902_, v_entry_2853_);
lean_dec(v___x_2902_);
if (v___x_2903_ == 0)
{
lean_object* v_toCold_2904_; lean_object* v_options_2905_; uint8_t v_hasTrace_2906_; 
v_toCold_2904_ = lean_ctor_get(v___y_2846_, 0);
v_options_2905_ = lean_ctor_get(v_toCold_2904_, 2);
v_hasTrace_2906_ = lean_ctor_get_uint8(v_options_2905_, sizeof(void*)*1);
if (v_hasTrace_2906_ == 0)
{
lean_dec(v_hint_2843_);
lean_dec(v_mod_2841_);
v___y_2860_ = v___y_2845_;
v___y_2861_ = v___y_2847_;
goto v___jp_2859_;
}
else
{
lean_object* v_inheritedTraceOptions_2907_; lean_object* v_cls_2908_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___x_2928_; uint8_t v___x_2929_; 
v_inheritedTraceOptions_2907_ = lean_ctor_get(v_toCold_2904_, 11);
v_cls_2908_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2));
v___x_2928_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10);
v___x_2929_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2907_, v_options_2905_, v___x_2928_);
if (v___x_2929_ == 0)
{
lean_dec(v_hint_2843_);
lean_dec(v_mod_2841_);
v___y_2860_ = v___y_2845_;
v___y_2861_ = v___y_2847_;
goto v___jp_2859_;
}
else
{
lean_object* v___x_2930_; lean_object* v___y_2932_; 
v___x_2930_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
if (v_isExporting_2852_ == 0)
{
lean_object* v___x_2939_; 
v___x_2939_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_2932_ = v___x_2939_;
goto v___jp_2931_;
}
else
{
lean_object* v___x_2940_; 
v___x_2940_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_2932_ = v___x_2940_;
goto v___jp_2931_;
}
v___jp_2931_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
lean_inc_ref(v___y_2932_);
v___x_2933_ = l_Lean_stringToMessageData(v___y_2932_);
v___x_2934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2930_);
lean_ctor_set(v___x_2934_, 1, v___x_2933_);
v___x_2935_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
v___x_2936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2934_);
lean_ctor_set(v___x_2936_, 1, v___x_2935_);
if (v_isMeta_2842_ == 0)
{
lean_object* v___x_2937_; 
v___x_2937_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15));
v___y_2915_ = v___x_2936_;
v___y_2916_ = v___x_2937_;
goto v___jp_2914_;
}
else
{
lean_object* v___x_2938_; 
v___x_2938_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16));
v___y_2915_ = v___x_2936_;
v___y_2916_ = v___x_2938_;
goto v___jp_2914_;
}
}
}
v___jp_2909_:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___y_2910_);
lean_ctor_set(v___x_2912_, 1, v___y_2911_);
v___x_2913_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2908_, v___x_2912_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_dec_ref_known(v___x_2913_, 1);
v___y_2860_ = v___y_2845_;
v___y_2861_ = v___y_2847_;
goto v___jp_2859_;
}
else
{
lean_dec_ref_known(v_entry_2853_, 1);
return v___x_2913_;
}
}
v___jp_2914_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; uint8_t v___x_2923_; 
lean_inc_ref(v___y_2916_);
v___x_2917_ = l_Lean_stringToMessageData(v___y_2916_);
v___x_2918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___y_2915_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
v___x_2919_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4);
v___x_2920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2918_);
lean_ctor_set(v___x_2920_, 1, v___x_2919_);
v___x_2921_ = l_Lean_MessageData_ofName(v_mod_2841_);
v___x_2922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2920_);
lean_ctor_set(v___x_2922_, 1, v___x_2921_);
v___x_2923_ = l_Lean_Name_isAnonymous(v_hint_2843_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2924_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_2925_ = l_Lean_MessageData_ofName(v_hint_2843_);
v___x_2926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2926_, 0, v___x_2924_);
lean_ctor_set(v___x_2926_, 1, v___x_2925_);
v___y_2910_ = v___x_2922_;
v___y_2911_ = v___x_2926_;
goto v___jp_2909_;
}
else
{
lean_object* v___x_2927_; 
lean_dec(v_hint_2843_);
v___x_2927_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7);
v___y_2910_ = v___x_2922_;
v___y_2911_ = v___x_2927_;
goto v___jp_2909_;
}
}
}
}
else
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
lean_dec_ref_known(v_entry_2853_, 1);
lean_dec(v_hint_2843_);
lean_dec(v_mod_2841_);
v___x_2941_ = lean_box(0);
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
return v___x_2942_;
}
v___jp_2859_:
{
lean_object* v___x_2862_; lean_object* v_toEnvExtension_2863_; lean_object* v_env_2864_; lean_object* v_nextMacroScope_2865_; lean_object* v_ngen_2866_; lean_object* v_auxDeclNGen_2867_; lean_object* v_traceState_2868_; lean_object* v_recordedDeps_2869_; lean_object* v_messages_2870_; lean_object* v_infoState_2871_; lean_object* v_snapshotTasks_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2900_; 
v___x_2862_ = lean_st_ref_take(v___y_2861_);
v_toEnvExtension_2863_ = lean_ctor_get(v___x_2856_, 0);
v_env_2864_ = lean_ctor_get(v___x_2862_, 0);
v_nextMacroScope_2865_ = lean_ctor_get(v___x_2862_, 1);
v_ngen_2866_ = lean_ctor_get(v___x_2862_, 2);
v_auxDeclNGen_2867_ = lean_ctor_get(v___x_2862_, 3);
v_traceState_2868_ = lean_ctor_get(v___x_2862_, 4);
v_recordedDeps_2869_ = lean_ctor_get(v___x_2862_, 6);
v_messages_2870_ = lean_ctor_get(v___x_2862_, 7);
v_infoState_2871_ = lean_ctor_get(v___x_2862_, 8);
v_snapshotTasks_2872_ = lean_ctor_get(v___x_2862_, 9);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2900_ == 0)
{
lean_object* v_unused_2901_; 
v_unused_2901_ = lean_ctor_get(v___x_2862_, 5);
lean_dec(v_unused_2901_);
v___x_2874_ = v___x_2862_;
v_isShared_2875_ = v_isSharedCheck_2900_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_snapshotTasks_2872_);
lean_inc(v_infoState_2871_);
lean_inc(v_messages_2870_);
lean_inc(v_recordedDeps_2869_);
lean_inc(v_traceState_2868_);
lean_inc(v_auxDeclNGen_2867_);
lean_inc(v_ngen_2866_);
lean_inc(v_nextMacroScope_2865_);
lean_inc(v_env_2864_);
lean_dec(v___x_2862_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2900_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v_asyncMode_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2880_; 
v_asyncMode_2876_ = lean_ctor_get(v_toEnvExtension_2863_, 2);
v___x_2877_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2856_, v_env_2864_, v_entry_2853_, v_asyncMode_2876_, v___x_2858_);
v___x_2878_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 5, v___x_2878_);
lean_ctor_set(v___x_2874_, 0, v___x_2877_);
v___x_2880_ = v___x_2874_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2877_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v_nextMacroScope_2865_);
lean_ctor_set(v_reuseFailAlloc_2899_, 2, v_ngen_2866_);
lean_ctor_set(v_reuseFailAlloc_2899_, 3, v_auxDeclNGen_2867_);
lean_ctor_set(v_reuseFailAlloc_2899_, 4, v_traceState_2868_);
lean_ctor_set(v_reuseFailAlloc_2899_, 5, v___x_2878_);
lean_ctor_set(v_reuseFailAlloc_2899_, 6, v_recordedDeps_2869_);
lean_ctor_set(v_reuseFailAlloc_2899_, 7, v_messages_2870_);
lean_ctor_set(v_reuseFailAlloc_2899_, 8, v_infoState_2871_);
lean_ctor_set(v_reuseFailAlloc_2899_, 9, v_snapshotTasks_2872_);
v___x_2880_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v_mctx_2883_; lean_object* v_zetaDeltaFVarIds_2884_; lean_object* v_postponed_2885_; lean_object* v_diag_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2897_; 
v___x_2881_ = lean_st_ref_put(v___y_2861_, v___x_2880_);
v___x_2882_ = lean_st_ref_take(v___y_2860_);
v_mctx_2883_ = lean_ctor_get(v___x_2882_, 0);
v_zetaDeltaFVarIds_2884_ = lean_ctor_get(v___x_2882_, 2);
v_postponed_2885_ = lean_ctor_get(v___x_2882_, 3);
v_diag_2886_ = lean_ctor_get(v___x_2882_, 4);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2897_ == 0)
{
lean_object* v_unused_2898_; 
v_unused_2898_ = lean_ctor_get(v___x_2882_, 1);
lean_dec(v_unused_2898_);
v___x_2888_ = v___x_2882_;
v_isShared_2889_ = v_isSharedCheck_2897_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_diag_2886_);
lean_inc(v_postponed_2885_);
lean_inc(v_zetaDeltaFVarIds_2884_);
lean_inc(v_mctx_2883_);
lean_dec(v___x_2882_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2897_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2893_; 
v___x_2890_ = lean_box(0);
v___x_2891_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 1, v___x_2891_);
v___x_2893_ = v___x_2888_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_mctx_2883_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v___x_2891_);
lean_ctor_set(v_reuseFailAlloc_2896_, 2, v_zetaDeltaFVarIds_2884_);
lean_ctor_set(v_reuseFailAlloc_2896_, 3, v_postponed_2885_);
lean_ctor_set(v_reuseFailAlloc_2896_, 4, v_diag_2886_);
v___x_2893_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = lean_st_ref_put(v___y_2860_, v___x_2893_);
v___x_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2890_);
return v___x_2895_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object* v_mod_2943_, lean_object* v_isMeta_2944_, lean_object* v_hint_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
uint8_t v_isMeta_boxed_2951_; lean_object* v_res_2952_; 
v_isMeta_boxed_2951_ = lean_unbox(v_isMeta_2944_);
v_res_2952_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_mod_2943_, v_isMeta_boxed_2951_, v_hint_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(lean_object* v_a_2953_, lean_object* v_x_2954_){
_start:
{
if (lean_obj_tag(v_x_2954_) == 0)
{
lean_object* v___x_2955_; 
v___x_2955_ = lean_box(0);
return v___x_2955_;
}
else
{
lean_object* v_key_2956_; lean_object* v_value_2957_; lean_object* v_tail_2958_; uint8_t v___x_2959_; 
v_key_2956_ = lean_ctor_get(v_x_2954_, 0);
v_value_2957_ = lean_ctor_get(v_x_2954_, 1);
v_tail_2958_ = lean_ctor_get(v_x_2954_, 2);
v___x_2959_ = lean_name_eq(v_key_2956_, v_a_2953_);
if (v___x_2959_ == 0)
{
v_x_2954_ = v_tail_2958_;
goto _start;
}
else
{
lean_object* v___x_2961_; 
lean_inc(v_value_2957_);
v___x_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2961_, 0, v_value_2957_);
return v___x_2961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_a_2962_, lean_object* v_x_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_2962_, v_x_2963_);
lean_dec(v_x_2963_);
lean_dec(v_a_2962_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(lean_object* v_m_2965_, lean_object* v_a_2966_){
_start:
{
lean_object* v_buckets_2967_; lean_object* v___x_2968_; uint64_t v___y_2970_; 
v_buckets_2967_ = lean_ctor_get(v_m_2965_, 1);
v___x_2968_ = lean_array_get_size(v_buckets_2967_);
if (lean_obj_tag(v_a_2966_) == 0)
{
uint64_t v___x_2984_; 
v___x_2984_ = 1723ULL;
v___y_2970_ = v___x_2984_;
goto v___jp_2969_;
}
else
{
uint64_t v_hash_2985_; 
v_hash_2985_ = lean_ctor_get_uint64(v_a_2966_, sizeof(void*)*2);
v___y_2970_ = v_hash_2985_;
goto v___jp_2969_;
}
v___jp_2969_:
{
uint64_t v___x_2971_; uint64_t v___x_2972_; uint64_t v_fold_2973_; uint64_t v___x_2974_; uint64_t v___x_2975_; uint64_t v___x_2976_; size_t v___x_2977_; size_t v___x_2978_; size_t v___x_2979_; size_t v___x_2980_; size_t v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2971_ = 32ULL;
v___x_2972_ = lean_uint64_shift_right(v___y_2970_, v___x_2971_);
v_fold_2973_ = lean_uint64_xor(v___y_2970_, v___x_2972_);
v___x_2974_ = 16ULL;
v___x_2975_ = lean_uint64_shift_right(v_fold_2973_, v___x_2974_);
v___x_2976_ = lean_uint64_xor(v_fold_2973_, v___x_2975_);
v___x_2977_ = lean_uint64_to_usize(v___x_2976_);
v___x_2978_ = lean_usize_of_nat(v___x_2968_);
v___x_2979_ = ((size_t)1ULL);
v___x_2980_ = lean_usize_sub(v___x_2978_, v___x_2979_);
v___x_2981_ = lean_usize_land(v___x_2977_, v___x_2980_);
v___x_2982_ = lean_array_uget_borrowed(v_buckets_2967_, v___x_2981_);
v___x_2983_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_2966_, v___x_2982_);
return v___x_2983_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg___boxed(lean_object* v_m_2986_, lean_object* v_a_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_2986_, v_a_2987_);
lean_dec(v_a_2987_);
lean_dec_ref(v_m_2986_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object* v___x_2989_, lean_object* v_declName_2990_, lean_object* v_as_2991_, size_t v_sz_2992_, size_t v_i_2993_, lean_object* v_b_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
uint8_t v___x_3000_; 
v___x_3000_ = lean_usize_dec_lt(v_i_2993_, v_sz_2992_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; 
lean_dec(v_declName_2990_);
v___x_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3001_, 0, v_b_2994_);
return v___x_3001_;
}
else
{
lean_object* v___x_3002_; lean_object* v_modules_3003_; lean_object* v___x_3004_; lean_object* v_a_3005_; lean_object* v___x_3006_; lean_object* v_toImport_3007_; lean_object* v_module_3008_; lean_object* v___x_3009_; uint8_t v___x_3010_; lean_object* v___x_3011_; 
v___x_3002_ = l_Lean_Environment_header(v___x_2989_);
v_modules_3003_ = lean_ctor_get(v___x_3002_, 3);
lean_inc_ref(v_modules_3003_);
lean_dec_ref(v___x_3002_);
v___x_3004_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3005_ = lean_array_uget_borrowed(v_as_2991_, v_i_2993_);
v___x_3006_ = lean_array_get(v___x_3004_, v_modules_3003_, v_a_3005_);
lean_dec_ref(v_modules_3003_);
v_toImport_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc_ref(v_toImport_3007_);
lean_dec(v___x_3006_);
v_module_3008_ = lean_ctor_get(v_toImport_3007_, 0);
lean_inc(v_module_3008_);
lean_dec_ref(v_toImport_3007_);
v___x_3009_ = lean_box(0);
v___x_3010_ = 0;
lean_inc(v_declName_2990_);
v___x_3011_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_3008_, v___x_3010_, v_declName_2990_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
if (lean_obj_tag(v___x_3011_) == 0)
{
size_t v___x_3012_; size_t v___x_3013_; 
lean_dec_ref_known(v___x_3011_, 1);
v___x_3012_ = ((size_t)1ULL);
v___x_3013_ = lean_usize_add(v_i_2993_, v___x_3012_);
v_i_2993_ = v___x_3013_;
v_b_2994_ = v___x_3009_;
goto _start;
}
else
{
lean_dec(v_declName_2990_);
return v___x_3011_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object* v___x_3015_, lean_object* v_declName_3016_, lean_object* v_as_3017_, lean_object* v_sz_3018_, lean_object* v_i_3019_, lean_object* v_b_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
size_t v_sz_boxed_3026_; size_t v_i_boxed_3027_; lean_object* v_res_3028_; 
v_sz_boxed_3026_ = lean_unbox_usize(v_sz_3018_);
lean_dec(v_sz_3018_);
v_i_boxed_3027_ = lean_unbox_usize(v_i_3019_);
lean_dec(v_i_3019_);
v_res_3028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v___x_3015_, v_declName_3016_, v_as_3017_, v_sz_boxed_3026_, v_i_boxed_3027_, v_b_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec_ref(v_as_3017_);
lean_dec_ref(v___x_3015_);
return v_res_3028_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0(void){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = l_Std_HashMap_instInhabited___redArg();
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object* v_declName_3032_, uint8_t v_isMeta_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v_env_3044_; lean_object* v___y_3046_; lean_object* v___x_3059_; 
v___x_3039_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0);
v___x_3040_ = lean_st_ref_get(v___y_3037_);
v_env_3044_ = lean_ctor_get(v___x_3040_, 0);
lean_inc_ref(v_env_3044_);
lean_dec(v___x_3040_);
v___x_3059_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3044_, v_declName_3032_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_dec_ref(v_env_3044_);
lean_dec(v_declName_3032_);
goto v___jp_3041_;
}
else
{
lean_object* v_val_3060_; lean_object* v___x_3061_; lean_object* v_modules_3062_; lean_object* v___x_3063_; uint8_t v___x_3064_; 
v_val_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_val_3060_);
lean_dec_ref_known(v___x_3059_, 1);
v___x_3061_ = l_Lean_Environment_header(v_env_3044_);
v_modules_3062_ = lean_ctor_get(v___x_3061_, 3);
lean_inc_ref(v_modules_3062_);
lean_dec_ref(v___x_3061_);
v___x_3063_ = lean_array_get_size(v_modules_3062_);
v___x_3064_ = lean_nat_dec_lt(v_val_3060_, v___x_3063_);
if (v___x_3064_ == 0)
{
lean_dec_ref(v_modules_3062_);
lean_dec(v_val_3060_);
lean_dec_ref(v_env_3044_);
lean_dec(v_declName_3032_);
goto v___jp_3041_;
}
else
{
lean_object* v___x_3065_; lean_object* v___x_3066_; uint8_t v___y_3068_; 
v___x_3065_ = lean_array_fget(v_modules_3062_, v_val_3060_);
lean_dec(v_val_3060_);
lean_dec_ref(v_modules_3062_);
v___x_3066_ = lean_st_ref_get(v___y_3037_);
if (v_isMeta_3033_ == 0)
{
lean_dec(v___x_3066_);
v___y_3068_ = v_isMeta_3033_;
goto v___jp_3067_;
}
else
{
lean_object* v_env_3079_; uint8_t v___x_3080_; 
v_env_3079_ = lean_ctor_get(v___x_3066_, 0);
lean_inc_ref(v_env_3079_);
lean_dec(v___x_3066_);
lean_inc(v_declName_3032_);
v___x_3080_ = l_Lean_isMarkedMeta(v_env_3079_, v_declName_3032_);
if (v___x_3080_ == 0)
{
v___y_3068_ = v_isMeta_3033_;
goto v___jp_3067_;
}
else
{
uint8_t v___x_3081_; 
v___x_3081_ = 0;
v___y_3068_ = v___x_3081_;
goto v___jp_3067_;
}
}
v___jp_3067_:
{
lean_object* v_toImport_3069_; lean_object* v_module_3070_; lean_object* v___x_3071_; 
v_toImport_3069_ = lean_ctor_get(v___x_3065_, 0);
lean_inc_ref(v_toImport_3069_);
lean_dec(v___x_3065_);
v_module_3070_ = lean_ctor_get(v_toImport_3069_, 0);
lean_inc(v_module_3070_);
lean_dec_ref(v_toImport_3069_);
lean_inc(v_declName_3032_);
v___x_3071_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_3070_, v___y_3068_, v_declName_3032_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
lean_dec_ref_known(v___x_3071_, 1);
v___x_3072_ = l_Lean_indirectModUseExt;
v___x_3073_ = lean_box(1);
v___x_3074_ = lean_box(0);
lean_inc_ref(v_env_3044_);
v___x_3075_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3039_, v___x_3072_, v_env_3044_, v___x_3073_, v___x_3074_);
v___x_3076_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3075_, v_declName_3032_);
lean_dec(v___x_3075_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v___x_3077_; 
v___x_3077_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___y_3046_ = v___x_3077_;
goto v___jp_3045_;
}
else
{
lean_object* v_val_3078_; 
v_val_3078_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_val_3078_);
lean_dec_ref_known(v___x_3076_, 1);
v___y_3046_ = v_val_3078_;
goto v___jp_3045_;
}
}
else
{
lean_dec_ref(v_env_3044_);
lean_dec(v_declName_3032_);
return v___x_3071_;
}
}
}
}
v___jp_3041_:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = lean_box(0);
v___x_3043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3042_);
return v___x_3043_;
}
v___jp_3045_:
{
lean_object* v___x_3047_; size_t v_sz_3048_; size_t v___x_3049_; lean_object* v___x_3050_; 
v___x_3047_ = lean_box(0);
v_sz_3048_ = lean_array_size(v___y_3046_);
v___x_3049_ = ((size_t)0ULL);
v___x_3050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v_env_3044_, v_declName_3032_, v___y_3046_, v_sz_3048_, v___x_3049_, v___x_3047_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
lean_dec_ref(v___y_3046_);
lean_dec_ref(v_env_3044_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3057_ == 0)
{
lean_object* v_unused_3058_; 
v_unused_3058_ = lean_ctor_get(v___x_3050_, 0);
lean_dec(v_unused_3058_);
v___x_3052_ = v___x_3050_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_dec(v___x_3050_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 0, v___x_3047_);
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_3047_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
else
{
return v___x_3050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object* v_declName_3082_, lean_object* v_isMeta_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
uint8_t v_isMeta_boxed_3089_; lean_object* v_res_3090_; 
v_isMeta_boxed_3089_ = lean_unbox(v_isMeta_3083_);
v_res_3090_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3082_, v_isMeta_boxed_3089_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
return v_res_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(lean_object* v___y_3091_, uint8_t v_isExporting_3092_, lean_object* v___x_3093_, lean_object* v___y_3094_, lean_object* v___x_3095_, lean_object* v_a_x3f_3096_){
_start:
{
lean_object* v___x_3098_; lean_object* v_env_3099_; lean_object* v_nextMacroScope_3100_; lean_object* v_ngen_3101_; lean_object* v_auxDeclNGen_3102_; lean_object* v_traceState_3103_; lean_object* v_recordedDeps_3104_; lean_object* v_messages_3105_; lean_object* v_infoState_3106_; lean_object* v_snapshotTasks_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3132_; 
v___x_3098_ = lean_st_ref_take(v___y_3091_);
v_env_3099_ = lean_ctor_get(v___x_3098_, 0);
v_nextMacroScope_3100_ = lean_ctor_get(v___x_3098_, 1);
v_ngen_3101_ = lean_ctor_get(v___x_3098_, 2);
v_auxDeclNGen_3102_ = lean_ctor_get(v___x_3098_, 3);
v_traceState_3103_ = lean_ctor_get(v___x_3098_, 4);
v_recordedDeps_3104_ = lean_ctor_get(v___x_3098_, 6);
v_messages_3105_ = lean_ctor_get(v___x_3098_, 7);
v_infoState_3106_ = lean_ctor_get(v___x_3098_, 8);
v_snapshotTasks_3107_ = lean_ctor_get(v___x_3098_, 9);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3132_ == 0)
{
lean_object* v_unused_3133_; 
v_unused_3133_ = lean_ctor_get(v___x_3098_, 5);
lean_dec(v_unused_3133_);
v___x_3109_ = v___x_3098_;
v_isShared_3110_ = v_isSharedCheck_3132_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_snapshotTasks_3107_);
lean_inc(v_infoState_3106_);
lean_inc(v_messages_3105_);
lean_inc(v_recordedDeps_3104_);
lean_inc(v_traceState_3103_);
lean_inc(v_auxDeclNGen_3102_);
lean_inc(v_ngen_3101_);
lean_inc(v_nextMacroScope_3100_);
lean_inc(v_env_3099_);
lean_dec(v___x_3098_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3132_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3111_; lean_object* v___x_3113_; 
v___x_3111_ = l_Lean_Environment_setExporting(v_env_3099_, v_isExporting_3092_);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 5, v___x_3093_);
lean_ctor_set(v___x_3109_, 0, v___x_3111_);
v___x_3113_ = v___x_3109_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3111_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_nextMacroScope_3100_);
lean_ctor_set(v_reuseFailAlloc_3131_, 2, v_ngen_3101_);
lean_ctor_set(v_reuseFailAlloc_3131_, 3, v_auxDeclNGen_3102_);
lean_ctor_set(v_reuseFailAlloc_3131_, 4, v_traceState_3103_);
lean_ctor_set(v_reuseFailAlloc_3131_, 5, v___x_3093_);
lean_ctor_set(v_reuseFailAlloc_3131_, 6, v_recordedDeps_3104_);
lean_ctor_set(v_reuseFailAlloc_3131_, 7, v_messages_3105_);
lean_ctor_set(v_reuseFailAlloc_3131_, 8, v_infoState_3106_);
lean_ctor_set(v_reuseFailAlloc_3131_, 9, v_snapshotTasks_3107_);
v___x_3113_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v_mctx_3116_; lean_object* v_zetaDeltaFVarIds_3117_; lean_object* v_postponed_3118_; lean_object* v_diag_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3129_; 
v___x_3114_ = lean_st_ref_put(v___y_3091_, v___x_3113_);
v___x_3115_ = lean_st_ref_take(v___y_3094_);
v_mctx_3116_ = lean_ctor_get(v___x_3115_, 0);
v_zetaDeltaFVarIds_3117_ = lean_ctor_get(v___x_3115_, 2);
v_postponed_3118_ = lean_ctor_get(v___x_3115_, 3);
v_diag_3119_ = lean_ctor_get(v___x_3115_, 4);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3129_ == 0)
{
lean_object* v_unused_3130_; 
v_unused_3130_ = lean_ctor_get(v___x_3115_, 1);
lean_dec(v_unused_3130_);
v___x_3121_ = v___x_3115_;
v_isShared_3122_ = v_isSharedCheck_3129_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_diag_3119_);
lean_inc(v_postponed_3118_);
lean_inc(v_zetaDeltaFVarIds_3117_);
lean_inc(v_mctx_3116_);
lean_dec(v___x_3115_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3129_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3123_; lean_object* v___x_3125_; 
v___x_3123_ = lean_box(0);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 1, v___x_3095_);
v___x_3125_ = v___x_3121_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_mctx_3116_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v___x_3095_);
lean_ctor_set(v_reuseFailAlloc_3128_, 2, v_zetaDeltaFVarIds_3117_);
lean_ctor_set(v_reuseFailAlloc_3128_, 3, v_postponed_3118_);
lean_ctor_set(v_reuseFailAlloc_3128_, 4, v_diag_3119_);
v___x_3125_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3126_ = lean_st_ref_put(v___y_3094_, v___x_3125_);
v___x_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3123_);
return v___x_3127_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0___boxed(lean_object* v___y_3134_, lean_object* v_isExporting_3135_, lean_object* v___x_3136_, lean_object* v___y_3137_, lean_object* v___x_3138_, lean_object* v_a_x3f_3139_, lean_object* v___y_3140_){
_start:
{
uint8_t v_isExporting_boxed_3141_; lean_object* v_res_3142_; 
v_isExporting_boxed_3141_ = lean_unbox(v_isExporting_3135_);
v_res_3142_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3134_, v_isExporting_boxed_3141_, v___x_3136_, v___y_3137_, v___x_3138_, v_a_x3f_3139_);
lean_dec(v_a_x3f_3139_);
lean_dec(v___y_3137_);
lean_dec(v___y_3134_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(lean_object* v_x_3143_, uint8_t v_isExporting_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v___x_3150_; lean_object* v_env_3151_; lean_object* v___x_3152_; uint8_t v_isModule_3153_; 
v___x_3150_ = lean_st_ref_get(v___y_3148_);
v_env_3151_ = lean_ctor_get(v___x_3150_, 0);
lean_inc_ref(v_env_3151_);
lean_dec(v___x_3150_);
v___x_3152_ = l_Lean_Environment_header(v_env_3151_);
v_isModule_3153_ = lean_ctor_get_uint8(v___x_3152_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3152_);
if (v_isModule_3153_ == 0)
{
lean_object* v___x_3154_; 
lean_dec_ref(v_env_3151_);
lean_inc(v___y_3148_);
lean_inc_ref(v___y_3147_);
lean_inc(v___y_3146_);
lean_inc_ref(v___y_3145_);
v___x_3154_ = lean_apply_5(v_x_3143_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, lean_box(0));
return v___x_3154_;
}
else
{
uint8_t v_isExporting_3155_; 
v_isExporting_3155_ = lean_ctor_get_uint8(v_env_3151_, sizeof(void*)*8);
lean_dec_ref(v_env_3151_);
if (v_isExporting_3144_ == 0)
{
if (v_isExporting_3155_ == 0)
{
lean_object* v___x_3222_; 
lean_inc(v___y_3148_);
lean_inc_ref(v___y_3147_);
lean_inc(v___y_3146_);
lean_inc_ref(v___y_3145_);
v___x_3222_ = lean_apply_5(v_x_3143_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, lean_box(0));
return v___x_3222_;
}
else
{
goto v___jp_3156_;
}
}
else
{
if (v_isExporting_3155_ == 0)
{
goto v___jp_3156_;
}
else
{
lean_object* v___x_3223_; 
lean_inc(v___y_3148_);
lean_inc_ref(v___y_3147_);
lean_inc(v___y_3146_);
lean_inc_ref(v___y_3145_);
v___x_3223_ = lean_apply_5(v_x_3143_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, lean_box(0));
return v___x_3223_;
}
}
v___jp_3156_:
{
lean_object* v___x_3157_; lean_object* v_env_3158_; lean_object* v_nextMacroScope_3159_; lean_object* v_ngen_3160_; lean_object* v_auxDeclNGen_3161_; lean_object* v_traceState_3162_; lean_object* v_recordedDeps_3163_; lean_object* v_messages_3164_; lean_object* v_infoState_3165_; lean_object* v_snapshotTasks_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3220_; 
v___x_3157_ = lean_st_ref_take(v___y_3148_);
v_env_3158_ = lean_ctor_get(v___x_3157_, 0);
v_nextMacroScope_3159_ = lean_ctor_get(v___x_3157_, 1);
v_ngen_3160_ = lean_ctor_get(v___x_3157_, 2);
v_auxDeclNGen_3161_ = lean_ctor_get(v___x_3157_, 3);
v_traceState_3162_ = lean_ctor_get(v___x_3157_, 4);
v_recordedDeps_3163_ = lean_ctor_get(v___x_3157_, 6);
v_messages_3164_ = lean_ctor_get(v___x_3157_, 7);
v_infoState_3165_ = lean_ctor_get(v___x_3157_, 8);
v_snapshotTasks_3166_ = lean_ctor_get(v___x_3157_, 9);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3220_ == 0)
{
lean_object* v_unused_3221_; 
v_unused_3221_ = lean_ctor_get(v___x_3157_, 5);
lean_dec(v_unused_3221_);
v___x_3168_ = v___x_3157_;
v_isShared_3169_ = v_isSharedCheck_3220_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_snapshotTasks_3166_);
lean_inc(v_infoState_3165_);
lean_inc(v_messages_3164_);
lean_inc(v_recordedDeps_3163_);
lean_inc(v_traceState_3162_);
lean_inc(v_auxDeclNGen_3161_);
lean_inc(v_ngen_3160_);
lean_inc(v_nextMacroScope_3159_);
lean_inc(v_env_3158_);
lean_dec(v___x_3157_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3220_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3173_; 
v___x_3170_ = l_Lean_Environment_setExporting(v_env_3158_, v_isExporting_3144_);
v___x_3171_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 5, v___x_3171_);
lean_ctor_set(v___x_3168_, 0, v___x_3170_);
v___x_3173_ = v___x_3168_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3170_);
lean_ctor_set(v_reuseFailAlloc_3219_, 1, v_nextMacroScope_3159_);
lean_ctor_set(v_reuseFailAlloc_3219_, 2, v_ngen_3160_);
lean_ctor_set(v_reuseFailAlloc_3219_, 3, v_auxDeclNGen_3161_);
lean_ctor_set(v_reuseFailAlloc_3219_, 4, v_traceState_3162_);
lean_ctor_set(v_reuseFailAlloc_3219_, 5, v___x_3171_);
lean_ctor_set(v_reuseFailAlloc_3219_, 6, v_recordedDeps_3163_);
lean_ctor_set(v_reuseFailAlloc_3219_, 7, v_messages_3164_);
lean_ctor_set(v_reuseFailAlloc_3219_, 8, v_infoState_3165_);
lean_ctor_set(v_reuseFailAlloc_3219_, 9, v_snapshotTasks_3166_);
v___x_3173_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v_mctx_3176_; lean_object* v_zetaDeltaFVarIds_3177_; lean_object* v_postponed_3178_; lean_object* v_diag_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3217_; 
v___x_3174_ = lean_st_ref_put(v___y_3148_, v___x_3173_);
v___x_3175_ = lean_st_ref_take(v___y_3146_);
v_mctx_3176_ = lean_ctor_get(v___x_3175_, 0);
v_zetaDeltaFVarIds_3177_ = lean_ctor_get(v___x_3175_, 2);
v_postponed_3178_ = lean_ctor_get(v___x_3175_, 3);
v_diag_3179_ = lean_ctor_get(v___x_3175_, 4);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3217_ == 0)
{
lean_object* v_unused_3218_; 
v_unused_3218_ = lean_ctor_get(v___x_3175_, 1);
lean_dec(v_unused_3218_);
v___x_3181_ = v___x_3175_;
v_isShared_3182_ = v_isSharedCheck_3217_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_diag_3179_);
lean_inc(v_postponed_3178_);
lean_inc(v_zetaDeltaFVarIds_3177_);
lean_inc(v_mctx_3176_);
lean_dec(v___x_3175_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3217_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3183_; lean_object* v___x_3185_; 
v___x_3183_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 1, v___x_3183_);
v___x_3185_ = v___x_3181_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_mctx_3176_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v___x_3183_);
lean_ctor_set(v_reuseFailAlloc_3216_, 2, v_zetaDeltaFVarIds_3177_);
lean_ctor_set(v_reuseFailAlloc_3216_, 3, v_postponed_3178_);
lean_ctor_set(v_reuseFailAlloc_3216_, 4, v_diag_3179_);
v___x_3185_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
lean_object* v___x_3186_; lean_object* v_r_3187_; 
v___x_3186_ = lean_st_ref_put(v___y_3146_, v___x_3185_);
lean_inc(v___y_3148_);
lean_inc_ref(v___y_3147_);
lean_inc(v___y_3146_);
lean_inc_ref(v___y_3145_);
v_r_3187_ = lean_apply_5(v_x_3143_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, lean_box(0));
if (lean_obj_tag(v_r_3187_) == 0)
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3204_; 
v_a_3188_ = lean_ctor_get(v_r_3187_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v_r_3187_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3190_ = v_r_3187_;
v_isShared_3191_ = v_isSharedCheck_3204_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v_r_3187_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3204_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3193_; 
lean_inc(v_a_3188_);
if (v_isShared_3191_ == 0)
{
lean_ctor_set_tag(v___x_3190_, 1);
v___x_3193_ = v___x_3190_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_a_3188_);
v___x_3193_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
lean_object* v___x_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
v___x_3194_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3148_, v_isExporting_3155_, v___x_3171_, v___y_3146_, v___x_3183_, v___x_3193_);
lean_dec_ref(v___x_3193_);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3201_ == 0)
{
lean_object* v_unused_3202_; 
v_unused_3202_ = lean_ctor_get(v___x_3194_, 0);
lean_dec(v_unused_3202_);
v___x_3196_ = v___x_3194_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_dec(v___x_3194_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 0, v_a_3188_);
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3188_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
v_a_3205_ = lean_ctor_get(v_r_3187_, 0);
lean_inc(v_a_3205_);
lean_dec_ref_known(v_r_3187_, 1);
v___x_3206_ = lean_box(0);
v___x_3207_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3148_, v_isExporting_3155_, v___x_3171_, v___y_3146_, v___x_3183_, v___x_3206_);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3214_ == 0)
{
lean_object* v_unused_3215_; 
v_unused_3215_ = lean_ctor_get(v___x_3207_, 0);
lean_dec(v_unused_3215_);
v___x_3209_ = v___x_3207_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_dec(v___x_3207_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
lean_ctor_set_tag(v___x_3209_, 1);
lean_ctor_set(v___x_3209_, 0, v_a_3205_);
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3205_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___boxed(lean_object* v_x_3224_, lean_object* v_isExporting_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
uint8_t v_isExporting_boxed_3231_; lean_object* v_res_3232_; 
v_isExporting_boxed_3231_ = lean_unbox(v_isExporting_3225_);
v_res_3232_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3224_, v_isExporting_boxed_3231_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object* v_x_3233_, uint8_t v_when_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
if (v_when_3234_ == 0)
{
lean_object* v___x_3240_; 
lean_inc(v___y_3238_);
lean_inc_ref(v___y_3237_);
lean_inc(v___y_3236_);
lean_inc_ref(v___y_3235_);
v___x_3240_ = lean_apply_5(v_x_3233_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, lean_box(0));
return v___x_3240_;
}
else
{
uint8_t v___x_3241_; lean_object* v___x_3242_; 
v___x_3241_ = 0;
v___x_3242_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3233_, v___x_3241_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
return v___x_3242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object* v_x_3243_, lean_object* v_when_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
uint8_t v_when_boxed_3250_; lean_object* v_res_3251_; 
v_when_boxed_3250_ = lean_unbox(v_when_3244_);
v_res_3251_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3243_, v_when_boxed_3250_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object* v_ext_3252_, uint8_t v_showInfo_3253_, uint8_t v_minIndexable_3254_, lean_object* v_attrName_3255_, lean_object* v___x_3256_, lean_object* v_declName_3257_, lean_object* v_stx_3258_, uint8_t v_attrKind_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
uint8_t v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___f_3268_; uint8_t v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___y_3285_; lean_object* v___x_3295_; 
v___x_3263_ = 0;
v___x_3264_ = lean_box(v___x_3263_);
v___x_3265_ = lean_box(v_attrKind_3259_);
v___x_3266_ = lean_box(v_showInfo_3253_);
v___x_3267_ = lean_box(v_minIndexable_3254_);
lean_inc(v_declName_3257_);
v___f_3268_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed), 13, 8);
lean_closure_set(v___f_3268_, 0, v_declName_3257_);
lean_closure_set(v___f_3268_, 1, v___x_3264_);
lean_closure_set(v___f_3268_, 2, v___x_3265_);
lean_closure_set(v___f_3268_, 3, v_stx_3258_);
lean_closure_set(v___f_3268_, 4, v_ext_3252_);
lean_closure_set(v___f_3268_, 5, v___x_3266_);
lean_closure_set(v___f_3268_, 6, v___x_3267_);
lean_closure_set(v___f_3268_, 7, v_attrName_3255_);
v___x_3269_ = 1;
v___x_3270_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_3271_ = lean_unsigned_to_nat(32u);
v___x_3272_ = lean_mk_empty_array_with_capacity(v___x_3271_);
lean_dec_ref(v___x_3272_);
v___x_3273_ = lean_unsigned_to_nat(0u);
v___x_3274_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_3275_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_3276_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5));
v___x_3277_ = lean_box(0);
lean_inc(v___x_3256_);
v___x_3278_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3278_, 0, v___x_3270_);
lean_ctor_set(v___x_3278_, 1, v___x_3256_);
lean_ctor_set(v___x_3278_, 2, v___x_3275_);
lean_ctor_set(v___x_3278_, 3, v___x_3276_);
lean_ctor_set(v___x_3278_, 4, v___x_3277_);
lean_ctor_set(v___x_3278_, 5, v___x_3273_);
lean_ctor_set(v___x_3278_, 6, v___x_3277_);
lean_ctor_set_uint8(v___x_3278_, sizeof(void*)*7, v___x_3263_);
lean_ctor_set_uint8(v___x_3278_, sizeof(void*)*7 + 1, v___x_3263_);
lean_ctor_set_uint8(v___x_3278_, sizeof(void*)*7 + 2, v___x_3263_);
lean_ctor_set_uint8(v___x_3278_, sizeof(void*)*7 + 3, v___x_3269_);
v___x_3279_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6);
v___x_3280_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_3281_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_3282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3279_);
lean_ctor_set(v___x_3282_, 1, v___x_3280_);
lean_ctor_set(v___x_3282_, 2, v___x_3256_);
lean_ctor_set(v___x_3282_, 3, v___x_3274_);
lean_ctor_set(v___x_3282_, 4, v___x_3281_);
v___x_3283_ = lean_st_mk_ref(v___x_3282_);
v___x_3295_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3257_, v___x_3263_, v___x_3278_, v___x_3283_, v___y_3260_, v___y_3261_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v___x_3296_; 
lean_dec_ref_known(v___x_3295_, 1);
v___x_3296_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v___f_3268_, v___x_3269_, v___x_3278_, v___x_3283_, v___y_3260_, v___y_3261_);
lean_dec_ref_known(v___x_3278_, 7);
v___y_3285_ = v___x_3296_;
goto v___jp_3284_;
}
else
{
lean_dec_ref_known(v___x_3278_, 7);
lean_dec_ref(v___f_3268_);
v___y_3285_ = v___x_3295_;
goto v___jp_3284_;
}
v___jp_3284_:
{
if (lean_obj_tag(v___y_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3294_; 
v_a_3286_ = lean_ctor_get(v___y_3285_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___y_3285_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3288_ = v___y_3285_;
v_isShared_3289_ = v_isSharedCheck_3294_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___y_3285_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3294_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3290_; lean_object* v___x_3292_; 
v___x_3290_ = lean_st_ref_get(v___x_3283_);
lean_dec(v___x_3283_);
lean_dec(v___x_3290_);
if (v_isShared_3289_ == 0)
{
v___x_3292_ = v___x_3288_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_a_3286_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
else
{
lean_dec(v___x_3283_);
return v___y_3285_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object* v_ext_3297_, lean_object* v_showInfo_3298_, lean_object* v_minIndexable_3299_, lean_object* v_attrName_3300_, lean_object* v___x_3301_, lean_object* v_declName_3302_, lean_object* v_stx_3303_, lean_object* v_attrKind_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
uint8_t v_showInfo_boxed_3308_; uint8_t v_minIndexable_boxed_3309_; uint8_t v_attrKind_boxed_3310_; lean_object* v_res_3311_; 
v_showInfo_boxed_3308_ = lean_unbox(v_showInfo_3298_);
v_minIndexable_boxed_3309_ = lean_unbox(v_minIndexable_3299_);
v_attrKind_boxed_3310_ = lean_unbox(v_attrKind_3304_);
v_res_3311_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(v_ext_3297_, v_showInfo_boxed_3308_, v_minIndexable_boxed_3309_, v_attrName_3300_, v___x_3301_, v_declName_3302_, v_stx_3303_, v_attrKind_boxed_3310_, v___y_3305_, v___y_3306_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object* v_attrName_3334_, uint8_t v_minIndexable_3335_, uint8_t v_showInfo_3336_, lean_object* v_ext_3337_, lean_object* v_ref_3338_){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___f_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___f_3345_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3391_; 
v___x_3340_ = lean_box(1);
v___x_3341_ = lean_box(v_showInfo_3336_);
lean_inc_n(v_attrName_3334_, 2);
lean_inc_ref(v_ext_3337_);
v___f_3342_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed), 8, 4);
lean_closure_set(v___f_3342_, 0, v_ext_3337_);
lean_closure_set(v___f_3342_, 1, v___x_3340_);
lean_closure_set(v___f_3342_, 2, v___x_3341_);
lean_closure_set(v___f_3342_, 3, v_attrName_3334_);
v___x_3343_ = lean_box(v_showInfo_3336_);
v___x_3344_ = lean_box(v_minIndexable_3335_);
v___f_3345_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed), 11, 5);
lean_closure_set(v___f_3345_, 0, v_ext_3337_);
lean_closure_set(v___f_3345_, 1, v___x_3343_);
lean_closure_set(v___f_3345_, 2, v___x_3344_);
lean_closure_set(v___f_3345_, 3, v_attrName_3334_);
lean_closure_set(v___f_3345_, 4, v___x_3340_);
if (v_minIndexable_3335_ == 0)
{
if (v_showInfo_3336_ == 0)
{
lean_inc(v_attrName_3334_);
v___y_3391_ = v_attrName_3334_;
goto v___jp_3390_;
}
else
{
lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19));
lean_inc(v_attrName_3334_);
v___x_3420_ = lean_name_append_after(v_attrName_3334_, v___x_3419_);
v___y_3391_ = v___x_3420_;
goto v___jp_3390_;
}
}
else
{
if (v_showInfo_3336_ == 0)
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20));
lean_inc(v_attrName_3334_);
v___x_3422_ = lean_name_append_after(v_attrName_3334_, v___x_3421_);
v___y_3391_ = v___x_3422_;
goto v___jp_3390_;
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21));
lean_inc(v_attrName_3334_);
v___x_3424_ = lean_name_append_after(v_attrName_3334_, v___x_3423_);
v___y_3391_ = v___x_3424_;
goto v___jp_3390_;
}
}
v___jp_3346_:
{
lean_object* v___x_3349_; uint8_t v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; uint8_t v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0));
v___x_3350_ = 1;
v___x_3351_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3334_, v___x_3350_);
v___x_3352_ = lean_string_append(v___x_3349_, v___x_3351_);
v___x_3353_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1));
v___x_3354_ = lean_string_append(v___x_3352_, v___x_3353_);
v___x_3355_ = lean_string_append(v___x_3354_, v___x_3351_);
v___x_3356_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2));
v___x_3357_ = lean_string_append(v___x_3355_, v___x_3356_);
v___x_3358_ = lean_string_append(v___x_3357_, v___x_3351_);
v___x_3359_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3));
v___x_3360_ = lean_string_append(v___x_3358_, v___x_3359_);
v___x_3361_ = lean_string_append(v___x_3360_, v___x_3351_);
v___x_3362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4));
v___x_3363_ = lean_string_append(v___x_3361_, v___x_3362_);
v___x_3364_ = lean_string_append(v___x_3363_, v___x_3351_);
v___x_3365_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5));
v___x_3366_ = lean_string_append(v___x_3364_, v___x_3365_);
v___x_3367_ = lean_string_append(v___x_3366_, v___x_3351_);
v___x_3368_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6));
v___x_3369_ = lean_string_append(v___x_3367_, v___x_3368_);
v___x_3370_ = lean_string_append(v___x_3369_, v___x_3351_);
v___x_3371_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7));
v___x_3372_ = lean_string_append(v___x_3370_, v___x_3371_);
v___x_3373_ = lean_string_append(v___x_3372_, v___x_3351_);
v___x_3374_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8));
v___x_3375_ = lean_string_append(v___x_3373_, v___x_3374_);
v___x_3376_ = lean_string_append(v___x_3375_, v___x_3351_);
v___x_3377_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9));
v___x_3378_ = lean_string_append(v___x_3376_, v___x_3377_);
v___x_3379_ = lean_string_append(v___x_3378_, v___x_3351_);
v___x_3380_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10));
v___x_3381_ = lean_string_append(v___x_3379_, v___x_3380_);
v___x_3382_ = lean_string_append(v___x_3381_, v___x_3351_);
lean_dec_ref(v___x_3351_);
v___x_3383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11));
v___x_3384_ = lean_string_append(v___x_3382_, v___x_3383_);
v___x_3385_ = lean_string_append(v___y_3348_, v___x_3384_);
lean_dec_ref(v___x_3384_);
v___x_3386_ = 1;
v___x_3387_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3387_, 0, v_ref_3338_);
lean_ctor_set(v___x_3387_, 1, v___y_3347_);
lean_ctor_set(v___x_3387_, 2, v___x_3385_);
lean_ctor_set_uint8(v___x_3387_, sizeof(void*)*3, v___x_3386_);
v___x_3388_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
lean_ctor_set(v___x_3388_, 1, v___f_3345_);
lean_ctor_set(v___x_3388_, 2, v___f_3342_);
v___x_3389_ = l_Lean_registerBuiltinAttribute(v___x_3388_);
return v___x_3389_;
}
v___jp_3390_:
{
if (v_minIndexable_3335_ == 0)
{
if (v_showInfo_3336_ == 0)
{
lean_object* v___x_3392_; uint8_t v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3392_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
v___x_3393_ = 1;
lean_inc(v_attrName_3334_);
v___x_3394_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3334_, v___x_3393_);
v___x_3395_ = lean_string_append(v___x_3392_, v___x_3394_);
lean_dec_ref(v___x_3394_);
v___x_3396_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13));
v___x_3397_ = lean_string_append(v___x_3395_, v___x_3396_);
v___y_3347_ = v___y_3391_;
v___y_3348_ = v___x_3397_;
goto v___jp_3346_;
}
else
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3398_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3334_);
v___x_3399_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3334_, v_showInfo_3336_);
v___x_3400_ = lean_string_append(v___x_3398_, v___x_3399_);
v___x_3401_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14));
v___x_3402_ = lean_string_append(v___x_3400_, v___x_3401_);
v___x_3403_ = lean_string_append(v___x_3402_, v___x_3399_);
lean_dec_ref(v___x_3399_);
v___x_3404_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15));
v___x_3405_ = lean_string_append(v___x_3403_, v___x_3404_);
v___y_3347_ = v___y_3391_;
v___y_3348_ = v___x_3405_;
goto v___jp_3346_;
}
}
else
{
if (v_showInfo_3336_ == 0)
{
lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3334_);
v___x_3407_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3334_, v_minIndexable_3335_);
v___x_3408_ = lean_string_append(v___x_3406_, v___x_3407_);
lean_dec_ref(v___x_3407_);
v___x_3409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16));
v___x_3410_ = lean_string_append(v___x_3408_, v___x_3409_);
v___y_3347_ = v___y_3391_;
v___y_3348_ = v___x_3410_;
goto v___jp_3346_;
}
else
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3334_);
v___x_3412_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3334_, v_showInfo_3336_);
v___x_3413_ = lean_string_append(v___x_3411_, v___x_3412_);
v___x_3414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17));
v___x_3415_ = lean_string_append(v___x_3413_, v___x_3414_);
v___x_3416_ = lean_string_append(v___x_3415_, v___x_3412_);
lean_dec_ref(v___x_3412_);
v___x_3417_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18));
v___x_3418_ = lean_string_append(v___x_3416_, v___x_3417_);
v___y_3347_ = v___y_3391_;
v___y_3348_ = v___x_3418_;
goto v___jp_3346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object* v_attrName_3425_, lean_object* v_minIndexable_3426_, lean_object* v_showInfo_3427_, lean_object* v_ext_3428_, lean_object* v_ref_3429_, lean_object* v_a_3430_){
_start:
{
uint8_t v_minIndexable_boxed_3431_; uint8_t v_showInfo_boxed_3432_; lean_object* v_res_3433_; 
v_minIndexable_boxed_3431_ = lean_unbox(v_minIndexable_3426_);
v_showInfo_boxed_3432_ = lean_unbox(v_showInfo_3427_);
v_res_3433_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3425_, v_minIndexable_boxed_3431_, v_showInfo_boxed_3432_, v_ext_3428_, v_ref_3429_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object* v_00_u03b1_3434_, lean_object* v_msg_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v___x_3441_; 
v___x_3441_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object* v_00_u03b1_3442_, lean_object* v_msg_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(v_00_u03b1_3442_, v_msg_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object* v_ext_3450_, uint8_t v_attrKind_3451_, uint8_t v_showInfo_3452_, uint8_t v_minIndexable_3453_, lean_object* v_as_3454_, lean_object* v_as_x27_3455_, lean_object* v_b_3456_, lean_object* v_a_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_){
_start:
{
lean_object* v___x_3463_; 
v___x_3463_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3450_, v_attrKind_3451_, v_showInfo_3452_, v_minIndexable_3453_, v_as_x27_3455_, v_b_3456_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
return v___x_3463_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object* v_ext_3464_, lean_object* v_attrKind_3465_, lean_object* v_showInfo_3466_, lean_object* v_minIndexable_3467_, lean_object* v_as_3468_, lean_object* v_as_x27_3469_, lean_object* v_b_3470_, lean_object* v_a_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
uint8_t v_attrKind_boxed_3477_; uint8_t v_showInfo_boxed_3478_; uint8_t v_minIndexable_boxed_3479_; lean_object* v_res_3480_; 
v_attrKind_boxed_3477_ = lean_unbox(v_attrKind_3465_);
v_showInfo_boxed_3478_ = lean_unbox(v_showInfo_3466_);
v_minIndexable_boxed_3479_ = lean_unbox(v_minIndexable_3467_);
v_res_3480_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(v_ext_3464_, v_attrKind_boxed_3477_, v_showInfo_boxed_3478_, v_minIndexable_boxed_3479_, v_as_3468_, v_as_x27_3469_, v_b_3470_, v_a_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v_as_x27_3469_);
lean_dec(v_as_3468_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(lean_object* v_00_u03b1_3481_, lean_object* v_x_3482_, uint8_t v_isExporting_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_){
_start:
{
lean_object* v___x_3489_; 
v___x_3489_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3482_, v_isExporting_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___boxed(lean_object* v_00_u03b1_3490_, lean_object* v_x_3491_, lean_object* v_isExporting_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
uint8_t v_isExporting_boxed_3498_; lean_object* v_res_3499_; 
v_isExporting_boxed_3498_ = lean_unbox(v_isExporting_3492_);
v_res_3499_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(v_00_u03b1_3490_, v_x_3491_, v_isExporting_boxed_3498_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object* v_00_u03b1_3500_, lean_object* v_x_3501_, uint8_t v_when_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3501_, v_when_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object* v_00_u03b1_3509_, lean_object* v_x_3510_, lean_object* v_when_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
uint8_t v_when_boxed_3517_; lean_object* v_res_3518_; 
v_when_boxed_3517_ = lean_unbox(v_when_3511_);
v_res_3518_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(v_00_u03b1_3509_, v_x_3510_, v_when_boxed_3517_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(lean_object* v_00_u03b2_3519_, lean_object* v_m_3520_, lean_object* v_a_3521_){
_start:
{
lean_object* v___x_3522_; 
v___x_3522_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_3520_, v_a_3521_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3523_, lean_object* v_m_3524_, lean_object* v_a_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(v_00_u03b2_3523_, v_m_3524_, v_a_3525_);
lean_dec(v_a_3525_);
lean_dec_ref(v_m_3524_);
return v_res_3526_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3527_, lean_object* v_x_3528_, lean_object* v_x_3529_){
_start:
{
uint8_t v___x_3530_; 
v___x_3530_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_3528_, v_x_3529_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3531_, lean_object* v_x_3532_, lean_object* v_x_3533_){
_start:
{
uint8_t v_res_3534_; lean_object* v_r_3535_; 
v_res_3534_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(v_00_u03b2_3531_, v_x_3532_, v_x_3533_);
lean_dec_ref(v_x_3533_);
lean_dec_ref(v_x_3532_);
v_r_3535_ = lean_box(v_res_3534_);
return v_r_3535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_3536_, lean_object* v_a_3537_, lean_object* v_x_3538_){
_start:
{
lean_object* v___x_3539_; 
v___x_3539_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_3537_, v_x_3538_);
return v___x_3539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3540_, lean_object* v_a_3541_, lean_object* v_x_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(v_00_u03b2_3540_, v_a_3541_, v_x_3542_);
lean_dec(v_x_3542_);
lean_dec(v_a_3541_);
return v_res_3543_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_3544_, lean_object* v_x_3545_, size_t v_x_3546_, lean_object* v_x_3547_){
_start:
{
uint8_t v___x_3548_; 
v___x_3548_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_3545_, v_x_3546_, v_x_3547_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3549_, lean_object* v_x_3550_, lean_object* v_x_3551_, lean_object* v_x_3552_){
_start:
{
size_t v_x_16926__boxed_3553_; uint8_t v_res_3554_; lean_object* v_r_3555_; 
v_x_16926__boxed_3553_ = lean_unbox_usize(v_x_3551_);
lean_dec(v_x_3551_);
v_res_3554_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(v_00_u03b2_3549_, v_x_3550_, v_x_16926__boxed_3553_, v_x_3552_);
lean_dec_ref(v_x_3552_);
lean_dec_ref(v_x_3550_);
v_r_3555_ = lean_box(v_res_3554_);
return v_r_3555_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_3556_, lean_object* v_keys_3557_, lean_object* v_vals_3558_, lean_object* v_heq_3559_, lean_object* v_i_3560_, lean_object* v_k_3561_){
_start:
{
uint8_t v___x_3562_; 
v___x_3562_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_3557_, v_i_3560_, v_k_3561_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_3563_, lean_object* v_keys_3564_, lean_object* v_vals_3565_, lean_object* v_heq_3566_, lean_object* v_i_3567_, lean_object* v_k_3568_){
_start:
{
uint8_t v_res_3569_; lean_object* v_r_3570_; 
v_res_3569_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(v_00_u03b2_3563_, v_keys_3564_, v_vals_3565_, v_heq_3566_, v_i_3567_, v_k_3568_);
lean_dec_ref(v_k_3568_);
lean_dec_ref(v_vals_3565_);
lean_dec_ref(v_keys_3564_);
v_r_3570_ = lean_box(v_res_3569_);
return v_r_3570_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3571_ = lean_box(0);
v___x_3572_ = lean_unsigned_to_nat(16u);
v___x_3573_ = lean_mk_array(v___x_3572_, v___x_3571_);
return v___x_3573_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3574_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3575_ = lean_unsigned_to_nat(0u);
v___x_3576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3575_);
lean_ctor_set(v___x_3576_, 1, v___x_3574_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3578_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3579_ = lean_st_mk_ref(v___x_3578_);
v___x_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object* v_a_3581_){
_start:
{
lean_object* v_res_3582_; 
v_res_3582_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object* v_cls_3583_, lean_object* v_msg_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_){
_start:
{
lean_object* v_ref_3588_; lean_object* v___x_3589_; lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3635_; 
v_ref_3588_ = lean_ctor_get(v___y_3585_, 2);
v___x_3589_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_3584_, v___y_3585_, v___y_3586_);
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3592_ = v___x_3589_;
v_isShared_3593_ = v_isSharedCheck_3635_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3589_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3635_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3594_; lean_object* v_traceState_3595_; lean_object* v_env_3596_; lean_object* v_nextMacroScope_3597_; lean_object* v_ngen_3598_; lean_object* v_auxDeclNGen_3599_; lean_object* v_cache_3600_; lean_object* v_recordedDeps_3601_; lean_object* v_messages_3602_; lean_object* v_infoState_3603_; lean_object* v_snapshotTasks_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3634_; 
v___x_3594_ = lean_st_ref_take(v___y_3586_);
v_traceState_3595_ = lean_ctor_get(v___x_3594_, 4);
v_env_3596_ = lean_ctor_get(v___x_3594_, 0);
v_nextMacroScope_3597_ = lean_ctor_get(v___x_3594_, 1);
v_ngen_3598_ = lean_ctor_get(v___x_3594_, 2);
v_auxDeclNGen_3599_ = lean_ctor_get(v___x_3594_, 3);
v_cache_3600_ = lean_ctor_get(v___x_3594_, 5);
v_recordedDeps_3601_ = lean_ctor_get(v___x_3594_, 6);
v_messages_3602_ = lean_ctor_get(v___x_3594_, 7);
v_infoState_3603_ = lean_ctor_get(v___x_3594_, 8);
v_snapshotTasks_3604_ = lean_ctor_get(v___x_3594_, 9);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3606_ = v___x_3594_;
v_isShared_3607_ = v_isSharedCheck_3634_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_snapshotTasks_3604_);
lean_inc(v_infoState_3603_);
lean_inc(v_messages_3602_);
lean_inc(v_recordedDeps_3601_);
lean_inc(v_cache_3600_);
lean_inc(v_traceState_3595_);
lean_inc(v_auxDeclNGen_3599_);
lean_inc(v_ngen_3598_);
lean_inc(v_nextMacroScope_3597_);
lean_inc(v_env_3596_);
lean_dec(v___x_3594_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3634_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
uint64_t v_tid_3608_; lean_object* v_traces_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3633_; 
v_tid_3608_ = lean_ctor_get_uint64(v_traceState_3595_, sizeof(void*)*1);
v_traces_3609_ = lean_ctor_get(v_traceState_3595_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v_traceState_3595_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3611_ = v_traceState_3595_;
v_isShared_3612_ = v_isSharedCheck_3633_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_traces_3609_);
lean_dec(v_traceState_3595_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3633_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; double v___x_3615_; uint8_t v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3624_; 
v___x_3613_ = lean_box(0);
v___x_3614_ = lean_box(0);
v___x_3615_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_3616_ = 0;
v___x_3617_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_3618_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3618_, 0, v_cls_3583_);
lean_ctor_set(v___x_3618_, 1, v___x_3614_);
lean_ctor_set(v___x_3618_, 2, v___x_3617_);
lean_ctor_set_float(v___x_3618_, sizeof(void*)*3, v___x_3615_);
lean_ctor_set_float(v___x_3618_, sizeof(void*)*3 + 8, v___x_3615_);
lean_ctor_set_uint8(v___x_3618_, sizeof(void*)*3 + 16, v___x_3616_);
v___x_3619_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_3620_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3618_);
lean_ctor_set(v___x_3620_, 1, v_a_3590_);
lean_ctor_set(v___x_3620_, 2, v___x_3619_);
lean_inc(v_ref_3588_);
v___x_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3621_, 0, v_ref_3588_);
lean_ctor_set(v___x_3621_, 1, v___x_3620_);
v___x_3622_ = l_Lean_PersistentArray_push___redArg(v_traces_3609_, v___x_3621_);
if (v_isShared_3612_ == 0)
{
lean_ctor_set(v___x_3611_, 0, v___x_3622_);
v___x_3624_ = v___x_3611_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3622_);
lean_ctor_set_uint64(v_reuseFailAlloc_3632_, sizeof(void*)*1, v_tid_3608_);
v___x_3624_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
lean_object* v___x_3626_; 
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 4, v___x_3624_);
v___x_3626_ = v___x_3606_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_env_3596_);
lean_ctor_set(v_reuseFailAlloc_3631_, 1, v_nextMacroScope_3597_);
lean_ctor_set(v_reuseFailAlloc_3631_, 2, v_ngen_3598_);
lean_ctor_set(v_reuseFailAlloc_3631_, 3, v_auxDeclNGen_3599_);
lean_ctor_set(v_reuseFailAlloc_3631_, 4, v___x_3624_);
lean_ctor_set(v_reuseFailAlloc_3631_, 5, v_cache_3600_);
lean_ctor_set(v_reuseFailAlloc_3631_, 6, v_recordedDeps_3601_);
lean_ctor_set(v_reuseFailAlloc_3631_, 7, v_messages_3602_);
lean_ctor_set(v_reuseFailAlloc_3631_, 8, v_infoState_3603_);
lean_ctor_set(v_reuseFailAlloc_3631_, 9, v_snapshotTasks_3604_);
v___x_3626_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
lean_object* v___x_3627_; lean_object* v___x_3629_; 
v___x_3627_ = lean_st_ref_put(v___y_3586_, v___x_3626_);
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 0, v___x_3613_);
v___x_3629_ = v___x_3592_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3613_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_cls_3636_, lean_object* v_msg_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3636_, v_msg_3637_, v___y_3638_, v___y_3639_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object* v_mod_3642_, uint8_t v_isMeta_3643_, lean_object* v_hint_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v_env_3650_; uint8_t v_isExporting_3651_; lean_object* v_entry_3652_; lean_object* v___x_3653_; lean_object* v_env_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___y_3659_; lean_object* v___x_3685_; uint8_t v___x_3686_; 
v___x_3648_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0);
v___x_3649_ = lean_st_ref_get(v___y_3646_);
v_env_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc_ref(v_env_3650_);
lean_dec(v___x_3649_);
v_isExporting_3651_ = lean_ctor_get_uint8(v_env_3650_, sizeof(void*)*8);
lean_dec_ref(v_env_3650_);
lean_inc(v_mod_3642_);
v_entry_3652_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3652_, 0, v_mod_3642_);
lean_ctor_set_uint8(v_entry_3652_, sizeof(void*)*1, v_isExporting_3651_);
lean_ctor_set_uint8(v_entry_3652_, sizeof(void*)*1 + 1, v_isMeta_3643_);
v___x_3653_ = lean_st_ref_get(v___y_3646_);
v_env_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc_ref(v_env_3654_);
lean_dec(v___x_3653_);
v___x_3655_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3656_ = lean_box(1);
v___x_3657_ = lean_box(0);
v___x_3685_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3648_, v___x_3655_, v_env_3654_, v___x_3656_, v___x_3657_);
v___x_3686_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_3685_, v_entry_3652_);
lean_dec(v___x_3685_);
if (v___x_3686_ == 0)
{
lean_object* v_toCold_3687_; lean_object* v_options_3688_; uint8_t v_hasTrace_3689_; 
v_toCold_3687_ = lean_ctor_get(v___y_3645_, 0);
v_options_3688_ = lean_ctor_get(v_toCold_3687_, 2);
v_hasTrace_3689_ = lean_ctor_get_uint8(v_options_3688_, sizeof(void*)*1);
if (v_hasTrace_3689_ == 0)
{
lean_dec(v_hint_3644_);
lean_dec(v_mod_3642_);
v___y_3659_ = v___y_3646_;
goto v___jp_3658_;
}
else
{
lean_object* v_inheritedTraceOptions_3690_; lean_object* v_cls_3691_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___x_3711_; uint8_t v___x_3712_; 
v_inheritedTraceOptions_3690_ = lean_ctor_get(v_toCold_3687_, 11);
v_cls_3691_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2));
v___x_3711_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10);
v___x_3712_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3690_, v_options_3688_, v___x_3711_);
if (v___x_3712_ == 0)
{
lean_dec(v_hint_3644_);
lean_dec(v_mod_3642_);
v___y_3659_ = v___y_3646_;
goto v___jp_3658_;
}
else
{
lean_object* v___x_3713_; lean_object* v___y_3715_; 
v___x_3713_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
if (v_isExporting_3651_ == 0)
{
lean_object* v___x_3722_; 
v___x_3722_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_3715_ = v___x_3722_;
goto v___jp_3714_;
}
else
{
lean_object* v___x_3723_; 
v___x_3723_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_3715_ = v___x_3723_;
goto v___jp_3714_;
}
v___jp_3714_:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
lean_inc_ref(v___y_3715_);
v___x_3716_ = l_Lean_stringToMessageData(v___y_3715_);
v___x_3717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3713_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
v___x_3718_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
v___x_3719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3717_);
lean_ctor_set(v___x_3719_, 1, v___x_3718_);
if (v_isMeta_3643_ == 0)
{
lean_object* v___x_3720_; 
v___x_3720_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15));
v___y_3698_ = v___x_3719_;
v___y_3699_ = v___x_3720_;
goto v___jp_3697_;
}
else
{
lean_object* v___x_3721_; 
v___x_3721_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16));
v___y_3698_ = v___x_3719_;
v___y_3699_ = v___x_3721_;
goto v___jp_3697_;
}
}
}
v___jp_3692_:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___y_3693_);
lean_ctor_set(v___x_3695_, 1, v___y_3694_);
v___x_3696_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3691_, v___x_3695_, v___y_3645_, v___y_3646_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_dec_ref_known(v___x_3696_, 1);
v___y_3659_ = v___y_3646_;
goto v___jp_3658_;
}
else
{
lean_dec_ref_known(v_entry_3652_, 1);
return v___x_3696_;
}
}
v___jp_3697_:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; uint8_t v___x_3706_; 
lean_inc_ref(v___y_3699_);
v___x_3700_ = l_Lean_stringToMessageData(v___y_3699_);
v___x_3701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3701_, 0, v___y_3698_);
lean_ctor_set(v___x_3701_, 1, v___x_3700_);
v___x_3702_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4);
v___x_3703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3701_);
lean_ctor_set(v___x_3703_, 1, v___x_3702_);
v___x_3704_ = l_Lean_MessageData_ofName(v_mod_3642_);
v___x_3705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3703_);
lean_ctor_set(v___x_3705_, 1, v___x_3704_);
v___x_3706_ = l_Lean_Name_isAnonymous(v_hint_3644_);
if (v___x_3706_ == 0)
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3707_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_3708_ = l_Lean_MessageData_ofName(v_hint_3644_);
v___x_3709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3707_);
lean_ctor_set(v___x_3709_, 1, v___x_3708_);
v___y_3693_ = v___x_3705_;
v___y_3694_ = v___x_3709_;
goto v___jp_3692_;
}
else
{
lean_object* v___x_3710_; 
lean_dec(v_hint_3644_);
v___x_3710_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7);
v___y_3693_ = v___x_3705_;
v___y_3694_ = v___x_3710_;
goto v___jp_3692_;
}
}
}
}
else
{
lean_object* v___x_3724_; lean_object* v___x_3725_; 
lean_dec_ref_known(v_entry_3652_, 1);
lean_dec(v_hint_3644_);
lean_dec(v_mod_3642_);
v___x_3724_ = lean_box(0);
v___x_3725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3724_);
return v___x_3725_;
}
v___jp_3658_:
{
lean_object* v___x_3660_; lean_object* v_toEnvExtension_3661_; lean_object* v_env_3662_; lean_object* v_nextMacroScope_3663_; lean_object* v_ngen_3664_; lean_object* v_auxDeclNGen_3665_; lean_object* v_traceState_3666_; lean_object* v_recordedDeps_3667_; lean_object* v_messages_3668_; lean_object* v_infoState_3669_; lean_object* v_snapshotTasks_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3683_; 
v___x_3660_ = lean_st_ref_take(v___y_3659_);
v_toEnvExtension_3661_ = lean_ctor_get(v___x_3655_, 0);
v_env_3662_ = lean_ctor_get(v___x_3660_, 0);
v_nextMacroScope_3663_ = lean_ctor_get(v___x_3660_, 1);
v_ngen_3664_ = lean_ctor_get(v___x_3660_, 2);
v_auxDeclNGen_3665_ = lean_ctor_get(v___x_3660_, 3);
v_traceState_3666_ = lean_ctor_get(v___x_3660_, 4);
v_recordedDeps_3667_ = lean_ctor_get(v___x_3660_, 6);
v_messages_3668_ = lean_ctor_get(v___x_3660_, 7);
v_infoState_3669_ = lean_ctor_get(v___x_3660_, 8);
v_snapshotTasks_3670_ = lean_ctor_get(v___x_3660_, 9);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3683_ == 0)
{
lean_object* v_unused_3684_; 
v_unused_3684_ = lean_ctor_get(v___x_3660_, 5);
lean_dec(v_unused_3684_);
v___x_3672_ = v___x_3660_;
v_isShared_3673_ = v_isSharedCheck_3683_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_snapshotTasks_3670_);
lean_inc(v_infoState_3669_);
lean_inc(v_messages_3668_);
lean_inc(v_recordedDeps_3667_);
lean_inc(v_traceState_3666_);
lean_inc(v_auxDeclNGen_3665_);
lean_inc(v_ngen_3664_);
lean_inc(v_nextMacroScope_3663_);
lean_inc(v_env_3662_);
lean_dec(v___x_3660_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3683_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v_asyncMode_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3679_; 
v_asyncMode_3674_ = lean_ctor_get(v_toEnvExtension_3661_, 2);
v___x_3675_ = lean_box(0);
v___x_3676_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3655_, v_env_3662_, v_entry_3652_, v_asyncMode_3674_, v___x_3657_);
v___x_3677_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 5, v___x_3677_);
lean_ctor_set(v___x_3672_, 0, v___x_3676_);
v___x_3679_ = v___x_3672_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3676_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v_nextMacroScope_3663_);
lean_ctor_set(v_reuseFailAlloc_3682_, 2, v_ngen_3664_);
lean_ctor_set(v_reuseFailAlloc_3682_, 3, v_auxDeclNGen_3665_);
lean_ctor_set(v_reuseFailAlloc_3682_, 4, v_traceState_3666_);
lean_ctor_set(v_reuseFailAlloc_3682_, 5, v___x_3677_);
lean_ctor_set(v_reuseFailAlloc_3682_, 6, v_recordedDeps_3667_);
lean_ctor_set(v_reuseFailAlloc_3682_, 7, v_messages_3668_);
lean_ctor_set(v_reuseFailAlloc_3682_, 8, v_infoState_3669_);
lean_ctor_set(v_reuseFailAlloc_3682_, 9, v_snapshotTasks_3670_);
v___x_3679_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3680_ = lean_st_ref_put(v___y_3659_, v___x_3679_);
v___x_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3675_);
return v___x_3681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object* v_mod_3726_, lean_object* v_isMeta_3727_, lean_object* v_hint_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_){
_start:
{
uint8_t v_isMeta_boxed_3732_; lean_object* v_res_3733_; 
v_isMeta_boxed_3732_ = lean_unbox(v_isMeta_3727_);
v_res_3733_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_mod_3726_, v_isMeta_boxed_3732_, v_hint_3728_, v___y_3729_, v___y_3730_);
lean_dec(v___y_3730_);
lean_dec_ref(v___y_3729_);
return v_res_3733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object* v___x_3734_, lean_object* v_declName_3735_, lean_object* v_as_3736_, size_t v_sz_3737_, size_t v_i_3738_, lean_object* v_b_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
uint8_t v___x_3743_; 
v___x_3743_ = lean_usize_dec_lt(v_i_3738_, v_sz_3737_);
if (v___x_3743_ == 0)
{
lean_object* v___x_3744_; 
lean_dec(v_declName_3735_);
v___x_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3744_, 0, v_b_3739_);
return v___x_3744_;
}
else
{
lean_object* v___x_3745_; lean_object* v_modules_3746_; lean_object* v___x_3747_; lean_object* v_a_3748_; lean_object* v___x_3749_; lean_object* v_toImport_3750_; lean_object* v_module_3751_; lean_object* v___x_3752_; uint8_t v___x_3753_; lean_object* v___x_3754_; 
v___x_3745_ = l_Lean_Environment_header(v___x_3734_);
v_modules_3746_ = lean_ctor_get(v___x_3745_, 3);
lean_inc_ref(v_modules_3746_);
lean_dec_ref(v___x_3745_);
v___x_3747_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3748_ = lean_array_uget_borrowed(v_as_3736_, v_i_3738_);
v___x_3749_ = lean_array_get(v___x_3747_, v_modules_3746_, v_a_3748_);
lean_dec_ref(v_modules_3746_);
v_toImport_3750_ = lean_ctor_get(v___x_3749_, 0);
lean_inc_ref(v_toImport_3750_);
lean_dec(v___x_3749_);
v_module_3751_ = lean_ctor_get(v_toImport_3750_, 0);
lean_inc(v_module_3751_);
lean_dec_ref(v_toImport_3750_);
v___x_3752_ = lean_box(0);
v___x_3753_ = 0;
lean_inc(v_declName_3735_);
v___x_3754_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3751_, v___x_3753_, v_declName_3735_, v___y_3740_, v___y_3741_);
if (lean_obj_tag(v___x_3754_) == 0)
{
size_t v___x_3755_; size_t v___x_3756_; 
lean_dec_ref_known(v___x_3754_, 1);
v___x_3755_ = ((size_t)1ULL);
v___x_3756_ = lean_usize_add(v_i_3738_, v___x_3755_);
v_i_3738_ = v___x_3756_;
v_b_3739_ = v___x_3752_;
goto _start;
}
else
{
lean_dec(v_declName_3735_);
return v___x_3754_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object* v___x_3758_, lean_object* v_declName_3759_, lean_object* v_as_3760_, lean_object* v_sz_3761_, lean_object* v_i_3762_, lean_object* v_b_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
size_t v_sz_boxed_3767_; size_t v_i_boxed_3768_; lean_object* v_res_3769_; 
v_sz_boxed_3767_ = lean_unbox_usize(v_sz_3761_);
lean_dec(v_sz_3761_);
v_i_boxed_3768_ = lean_unbox_usize(v_i_3762_);
lean_dec(v_i_3762_);
v_res_3769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v___x_3758_, v_declName_3759_, v_as_3760_, v_sz_boxed_3767_, v_i_boxed_3768_, v_b_3763_, v___y_3764_, v___y_3765_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
lean_dec_ref(v_as_3760_);
lean_dec_ref(v___x_3758_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object* v_declName_3770_, uint8_t v_isMeta_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v_env_3780_; lean_object* v___y_3782_; lean_object* v___x_3795_; 
v___x_3775_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0);
v___x_3776_ = lean_st_ref_get(v___y_3773_);
v_env_3780_ = lean_ctor_get(v___x_3776_, 0);
lean_inc_ref(v_env_3780_);
lean_dec(v___x_3776_);
v___x_3795_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3780_, v_declName_3770_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_dec_ref(v_env_3780_);
lean_dec(v_declName_3770_);
goto v___jp_3777_;
}
else
{
lean_object* v_val_3796_; lean_object* v___x_3797_; lean_object* v_modules_3798_; lean_object* v___x_3799_; uint8_t v___x_3800_; 
v_val_3796_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_val_3796_);
lean_dec_ref_known(v___x_3795_, 1);
v___x_3797_ = l_Lean_Environment_header(v_env_3780_);
v_modules_3798_ = lean_ctor_get(v___x_3797_, 3);
lean_inc_ref(v_modules_3798_);
lean_dec_ref(v___x_3797_);
v___x_3799_ = lean_array_get_size(v_modules_3798_);
v___x_3800_ = lean_nat_dec_lt(v_val_3796_, v___x_3799_);
if (v___x_3800_ == 0)
{
lean_dec_ref(v_modules_3798_);
lean_dec(v_val_3796_);
lean_dec_ref(v_env_3780_);
lean_dec(v_declName_3770_);
goto v___jp_3777_;
}
else
{
lean_object* v___x_3801_; lean_object* v___x_3802_; uint8_t v___y_3804_; 
v___x_3801_ = lean_array_fget(v_modules_3798_, v_val_3796_);
lean_dec(v_val_3796_);
lean_dec_ref(v_modules_3798_);
v___x_3802_ = lean_st_ref_get(v___y_3773_);
if (v_isMeta_3771_ == 0)
{
lean_dec(v___x_3802_);
v___y_3804_ = v_isMeta_3771_;
goto v___jp_3803_;
}
else
{
lean_object* v_env_3815_; uint8_t v___x_3816_; 
v_env_3815_ = lean_ctor_get(v___x_3802_, 0);
lean_inc_ref(v_env_3815_);
lean_dec(v___x_3802_);
lean_inc(v_declName_3770_);
v___x_3816_ = l_Lean_isMarkedMeta(v_env_3815_, v_declName_3770_);
if (v___x_3816_ == 0)
{
v___y_3804_ = v_isMeta_3771_;
goto v___jp_3803_;
}
else
{
uint8_t v___x_3817_; 
v___x_3817_ = 0;
v___y_3804_ = v___x_3817_;
goto v___jp_3803_;
}
}
v___jp_3803_:
{
lean_object* v_toImport_3805_; lean_object* v_module_3806_; lean_object* v___x_3807_; 
v_toImport_3805_ = lean_ctor_get(v___x_3801_, 0);
lean_inc_ref(v_toImport_3805_);
lean_dec(v___x_3801_);
v_module_3806_ = lean_ctor_get(v_toImport_3805_, 0);
lean_inc(v_module_3806_);
lean_dec_ref(v_toImport_3805_);
lean_inc(v_declName_3770_);
v___x_3807_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3806_, v___y_3804_, v_declName_3770_, v___y_3772_, v___y_3773_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
lean_dec_ref_known(v___x_3807_, 1);
v___x_3808_ = l_Lean_indirectModUseExt;
v___x_3809_ = lean_box(1);
v___x_3810_ = lean_box(0);
lean_inc_ref(v_env_3780_);
v___x_3811_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3775_, v___x_3808_, v_env_3780_, v___x_3809_, v___x_3810_);
v___x_3812_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3811_, v_declName_3770_);
lean_dec(v___x_3811_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v___x_3813_; 
v___x_3813_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___y_3782_ = v___x_3813_;
goto v___jp_3781_;
}
else
{
lean_object* v_val_3814_; 
v_val_3814_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_val_3814_);
lean_dec_ref_known(v___x_3812_, 1);
v___y_3782_ = v_val_3814_;
goto v___jp_3781_;
}
}
else
{
lean_dec_ref(v_env_3780_);
lean_dec(v_declName_3770_);
return v___x_3807_;
}
}
}
}
v___jp_3777_:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3778_ = lean_box(0);
v___x_3779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3778_);
return v___x_3779_;
}
v___jp_3781_:
{
lean_object* v___x_3783_; size_t v_sz_3784_; size_t v___x_3785_; lean_object* v___x_3786_; 
v___x_3783_ = lean_box(0);
v_sz_3784_ = lean_array_size(v___y_3782_);
v___x_3785_ = ((size_t)0ULL);
v___x_3786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v_env_3780_, v_declName_3770_, v___y_3782_, v_sz_3784_, v___x_3785_, v___x_3783_, v___y_3772_, v___y_3773_);
lean_dec_ref(v___y_3782_);
lean_dec_ref(v_env_3780_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3793_ == 0)
{
lean_object* v_unused_3794_; 
v_unused_3794_ = lean_ctor_get(v___x_3786_, 0);
lean_dec(v_unused_3794_);
v___x_3788_ = v___x_3786_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_dec(v___x_3786_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 0, v___x_3783_);
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3783_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
else
{
return v___x_3786_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object* v_declName_3818_, lean_object* v_isMeta_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
uint8_t v_isMeta_boxed_3823_; lean_object* v_res_3824_; 
v_isMeta_boxed_3823_ = lean_unbox(v_isMeta_3819_);
v_res_3824_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_declName_3818_, v_isMeta_boxed_3823_, v___y_3820_, v___y_3821_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
return v_res_3824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object* v_attrName_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_){
_start:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3829_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_3830_ = lean_st_ref_get(v___x_3829_);
v___x_3831_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3830_, v_attrName_3825_);
lean_dec(v___x_3830_);
if (lean_obj_tag(v___x_3831_) == 1)
{
lean_object* v_val_3832_; lean_object* v_ext_3833_; lean_object* v_name_3834_; uint8_t v___x_3835_; lean_object* v___x_3836_; 
v_val_3832_ = lean_ctor_get(v___x_3831_, 0);
v_ext_3833_ = lean_ctor_get(v_val_3832_, 1);
v_name_3834_ = lean_ctor_get(v_ext_3833_, 1);
v___x_3835_ = 1;
lean_inc(v_name_3834_);
v___x_3836_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_name_3834_, v___x_3835_, v_a_3826_, v_a_3827_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3843_; 
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3843_ == 0)
{
lean_object* v_unused_3844_; 
v_unused_3844_ = lean_ctor_get(v___x_3836_, 0);
lean_dec(v_unused_3844_);
v___x_3838_ = v___x_3836_;
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
else
{
lean_dec(v___x_3836_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3841_; 
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 0, v___x_3831_);
v___x_3841_ = v___x_3838_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3831_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
else
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3852_; 
lean_dec_ref_known(v___x_3831_, 1);
v_a_3845_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3847_ = v___x_3836_;
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3836_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
else
{
lean_object* v___x_3853_; 
v___x_3853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3831_);
return v___x_3853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object* v_attrName_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l_Lean_Meta_Grind_getExtension_x3f(v_attrName_3854_, v_a_3855_, v_a_3856_);
lean_dec(v_a_3856_);
lean_dec_ref(v_a_3855_);
lean_dec(v_attrName_3854_);
return v_res_3858_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerAttr___auto__1(void){
_start:
{
lean_object* v___x_3859_; 
v___x_3859_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_3859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_3860_, lean_object* v_x_3861_){
_start:
{
if (lean_obj_tag(v_x_3861_) == 0)
{
return v_x_3860_;
}
else
{
lean_object* v_key_3862_; lean_object* v_value_3863_; lean_object* v_tail_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3890_; 
v_key_3862_ = lean_ctor_get(v_x_3861_, 0);
v_value_3863_ = lean_ctor_get(v_x_3861_, 1);
v_tail_3864_ = lean_ctor_get(v_x_3861_, 2);
v_isSharedCheck_3890_ = !lean_is_exclusive(v_x_3861_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3866_ = v_x_3861_;
v_isShared_3867_ = v_isSharedCheck_3890_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_tail_3864_);
lean_inc(v_value_3863_);
lean_inc(v_key_3862_);
lean_dec(v_x_3861_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3890_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3868_; uint64_t v___y_3870_; 
v___x_3868_ = lean_array_get_size(v_x_3860_);
if (lean_obj_tag(v_key_3862_) == 0)
{
uint64_t v___x_3888_; 
v___x_3888_ = 1723ULL;
v___y_3870_ = v___x_3888_;
goto v___jp_3869_;
}
else
{
uint64_t v_hash_3889_; 
v_hash_3889_ = lean_ctor_get_uint64(v_key_3862_, sizeof(void*)*2);
v___y_3870_ = v_hash_3889_;
goto v___jp_3869_;
}
v___jp_3869_:
{
uint64_t v___x_3871_; uint64_t v___x_3872_; uint64_t v_fold_3873_; uint64_t v___x_3874_; uint64_t v___x_3875_; uint64_t v___x_3876_; size_t v___x_3877_; size_t v___x_3878_; size_t v___x_3879_; size_t v___x_3880_; size_t v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3884_; 
v___x_3871_ = 32ULL;
v___x_3872_ = lean_uint64_shift_right(v___y_3870_, v___x_3871_);
v_fold_3873_ = lean_uint64_xor(v___y_3870_, v___x_3872_);
v___x_3874_ = 16ULL;
v___x_3875_ = lean_uint64_shift_right(v_fold_3873_, v___x_3874_);
v___x_3876_ = lean_uint64_xor(v_fold_3873_, v___x_3875_);
v___x_3877_ = lean_uint64_to_usize(v___x_3876_);
v___x_3878_ = lean_usize_of_nat(v___x_3868_);
v___x_3879_ = ((size_t)1ULL);
v___x_3880_ = lean_usize_sub(v___x_3878_, v___x_3879_);
v___x_3881_ = lean_usize_land(v___x_3877_, v___x_3880_);
v___x_3882_ = lean_array_uget_borrowed(v_x_3860_, v___x_3881_);
lean_inc(v___x_3882_);
if (v_isShared_3867_ == 0)
{
lean_ctor_set(v___x_3866_, 2, v___x_3882_);
v___x_3884_ = v___x_3866_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_key_3862_);
lean_ctor_set(v_reuseFailAlloc_3887_, 1, v_value_3863_);
lean_ctor_set(v_reuseFailAlloc_3887_, 2, v___x_3882_);
v___x_3884_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
lean_object* v___x_3885_; 
v___x_3885_ = lean_array_uset(v_x_3860_, v___x_3881_, v___x_3884_);
v_x_3860_ = v___x_3885_;
v_x_3861_ = v_tail_3864_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_3891_, lean_object* v_source_3892_, lean_object* v_target_3893_){
_start:
{
lean_object* v___x_3894_; uint8_t v___x_3895_; 
v___x_3894_ = lean_array_get_size(v_source_3892_);
v___x_3895_ = lean_nat_dec_lt(v_i_3891_, v___x_3894_);
if (v___x_3895_ == 0)
{
lean_dec_ref(v_source_3892_);
lean_dec(v_i_3891_);
return v_target_3893_;
}
else
{
lean_object* v_es_3896_; lean_object* v___x_3897_; lean_object* v_source_3898_; lean_object* v_target_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v_es_3896_ = lean_array_fget(v_source_3892_, v_i_3891_);
v___x_3897_ = lean_box(0);
v_source_3898_ = lean_array_fset(v_source_3892_, v_i_3891_, v___x_3897_);
v_target_3899_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_3893_, v_es_3896_);
v___x_3900_ = lean_unsigned_to_nat(1u);
v___x_3901_ = lean_nat_add(v_i_3891_, v___x_3900_);
lean_dec(v_i_3891_);
v_i_3891_ = v___x_3901_;
v_source_3892_ = v_source_3898_;
v_target_3893_ = v_target_3899_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object* v_data_3903_){
_start:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v_nbuckets_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3904_ = lean_array_get_size(v_data_3903_);
v___x_3905_ = lean_unsigned_to_nat(2u);
v_nbuckets_3906_ = lean_nat_mul(v___x_3904_, v___x_3905_);
v___x_3907_ = lean_unsigned_to_nat(0u);
v___x_3908_ = lean_box(0);
v___x_3909_ = lean_mk_array(v_nbuckets_3906_, v___x_3908_);
v___x_3910_ = lean_array_propagate_mark(v_data_3903_, v___x_3909_);
v___x_3911_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v___x_3907_, v_data_3903_, v___x_3910_);
return v___x_3911_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object* v_a_3912_, lean_object* v_x_3913_){
_start:
{
if (lean_obj_tag(v_x_3913_) == 0)
{
uint8_t v___x_3914_; 
v___x_3914_ = 0;
return v___x_3914_;
}
else
{
lean_object* v_key_3915_; lean_object* v_tail_3916_; uint8_t v___x_3917_; 
v_key_3915_ = lean_ctor_get(v_x_3913_, 0);
v_tail_3916_ = lean_ctor_get(v_x_3913_, 2);
v___x_3917_ = lean_name_eq(v_key_3915_, v_a_3912_);
if (v___x_3917_ == 0)
{
v_x_3913_ = v_tail_3916_;
goto _start;
}
else
{
return v___x_3917_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_3919_, lean_object* v_x_3920_){
_start:
{
uint8_t v_res_3921_; lean_object* v_r_3922_; 
v_res_3921_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3919_, v_x_3920_);
lean_dec(v_x_3920_);
lean_dec(v_a_3919_);
v_r_3922_ = lean_box(v_res_3921_);
return v_r_3922_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object* v_a_3923_, lean_object* v_b_3924_, lean_object* v_x_3925_){
_start:
{
if (lean_obj_tag(v_x_3925_) == 0)
{
lean_dec(v_b_3924_);
lean_dec(v_a_3923_);
return v_x_3925_;
}
else
{
lean_object* v_key_3926_; lean_object* v_value_3927_; lean_object* v_tail_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3940_; 
v_key_3926_ = lean_ctor_get(v_x_3925_, 0);
v_value_3927_ = lean_ctor_get(v_x_3925_, 1);
v_tail_3928_ = lean_ctor_get(v_x_3925_, 2);
v_isSharedCheck_3940_ = !lean_is_exclusive(v_x_3925_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3930_ = v_x_3925_;
v_isShared_3931_ = v_isSharedCheck_3940_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_tail_3928_);
lean_inc(v_value_3927_);
lean_inc(v_key_3926_);
lean_dec(v_x_3925_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3940_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
uint8_t v___x_3932_; 
v___x_3932_ = lean_name_eq(v_key_3926_, v_a_3923_);
if (v___x_3932_ == 0)
{
lean_object* v___x_3933_; lean_object* v___x_3935_; 
v___x_3933_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3923_, v_b_3924_, v_tail_3928_);
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 2, v___x_3933_);
v___x_3935_ = v___x_3930_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_key_3926_);
lean_ctor_set(v_reuseFailAlloc_3936_, 1, v_value_3927_);
lean_ctor_set(v_reuseFailAlloc_3936_, 2, v___x_3933_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
else
{
lean_object* v___x_3938_; 
lean_dec(v_value_3927_);
lean_dec(v_key_3926_);
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 1, v_b_3924_);
lean_ctor_set(v___x_3930_, 0, v_a_3923_);
v___x_3938_ = v___x_3930_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3923_);
lean_ctor_set(v_reuseFailAlloc_3939_, 1, v_b_3924_);
lean_ctor_set(v_reuseFailAlloc_3939_, 2, v_tail_3928_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object* v_m_3941_, lean_object* v_a_3942_, lean_object* v_b_3943_){
_start:
{
lean_object* v_size_3944_; lean_object* v_buckets_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3991_; 
v_size_3944_ = lean_ctor_get(v_m_3941_, 0);
v_buckets_3945_ = lean_ctor_get(v_m_3941_, 1);
v_isSharedCheck_3991_ = !lean_is_exclusive(v_m_3941_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3947_ = v_m_3941_;
v_isShared_3948_ = v_isSharedCheck_3991_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_buckets_3945_);
lean_inc(v_size_3944_);
lean_dec(v_m_3941_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3991_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3949_; uint64_t v___y_3951_; 
v___x_3949_ = lean_array_get_size(v_buckets_3945_);
if (lean_obj_tag(v_a_3942_) == 0)
{
uint64_t v___x_3989_; 
v___x_3989_ = 1723ULL;
v___y_3951_ = v___x_3989_;
goto v___jp_3950_;
}
else
{
uint64_t v_hash_3990_; 
v_hash_3990_ = lean_ctor_get_uint64(v_a_3942_, sizeof(void*)*2);
v___y_3951_ = v_hash_3990_;
goto v___jp_3950_;
}
v___jp_3950_:
{
uint64_t v___x_3952_; uint64_t v___x_3953_; uint64_t v_fold_3954_; uint64_t v___x_3955_; uint64_t v___x_3956_; uint64_t v___x_3957_; size_t v___x_3958_; size_t v___x_3959_; size_t v___x_3960_; size_t v___x_3961_; size_t v___x_3962_; lean_object* v_bkt_3963_; uint8_t v___x_3964_; 
v___x_3952_ = 32ULL;
v___x_3953_ = lean_uint64_shift_right(v___y_3951_, v___x_3952_);
v_fold_3954_ = lean_uint64_xor(v___y_3951_, v___x_3953_);
v___x_3955_ = 16ULL;
v___x_3956_ = lean_uint64_shift_right(v_fold_3954_, v___x_3955_);
v___x_3957_ = lean_uint64_xor(v_fold_3954_, v___x_3956_);
v___x_3958_ = lean_uint64_to_usize(v___x_3957_);
v___x_3959_ = lean_usize_of_nat(v___x_3949_);
v___x_3960_ = ((size_t)1ULL);
v___x_3961_ = lean_usize_sub(v___x_3959_, v___x_3960_);
v___x_3962_ = lean_usize_land(v___x_3958_, v___x_3961_);
v_bkt_3963_ = lean_array_uget_borrowed(v_buckets_3945_, v___x_3962_);
v___x_3964_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3942_, v_bkt_3963_);
if (v___x_3964_ == 0)
{
lean_object* v___x_3965_; lean_object* v_size_x27_3966_; lean_object* v___x_3967_; lean_object* v_buckets_x27_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; uint8_t v___x_3974_; 
v___x_3965_ = lean_unsigned_to_nat(1u);
v_size_x27_3966_ = lean_nat_add(v_size_3944_, v___x_3965_);
lean_dec(v_size_3944_);
lean_inc(v_bkt_3963_);
v___x_3967_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3967_, 0, v_a_3942_);
lean_ctor_set(v___x_3967_, 1, v_b_3943_);
lean_ctor_set(v___x_3967_, 2, v_bkt_3963_);
v_buckets_x27_3968_ = lean_array_uset(v_buckets_3945_, v___x_3962_, v___x_3967_);
v___x_3969_ = lean_unsigned_to_nat(4u);
v___x_3970_ = lean_nat_mul(v_size_x27_3966_, v___x_3969_);
v___x_3971_ = lean_unsigned_to_nat(3u);
v___x_3972_ = lean_nat_div(v___x_3970_, v___x_3971_);
lean_dec(v___x_3970_);
v___x_3973_ = lean_array_get_size(v_buckets_x27_3968_);
v___x_3974_ = lean_nat_dec_le(v___x_3972_, v___x_3973_);
lean_dec(v___x_3972_);
if (v___x_3974_ == 0)
{
lean_object* v_val_3975_; lean_object* v___x_3977_; 
v_val_3975_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_buckets_x27_3968_);
if (v_isShared_3948_ == 0)
{
lean_ctor_set(v___x_3947_, 1, v_val_3975_);
lean_ctor_set(v___x_3947_, 0, v_size_x27_3966_);
v___x_3977_ = v___x_3947_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_size_x27_3966_);
lean_ctor_set(v_reuseFailAlloc_3978_, 1, v_val_3975_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
else
{
lean_object* v___x_3980_; 
if (v_isShared_3948_ == 0)
{
lean_ctor_set(v___x_3947_, 1, v_buckets_x27_3968_);
lean_ctor_set(v___x_3947_, 0, v_size_x27_3966_);
v___x_3980_ = v___x_3947_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_size_x27_3966_);
lean_ctor_set(v_reuseFailAlloc_3981_, 1, v_buckets_x27_3968_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
else
{
lean_object* v___x_3982_; lean_object* v_buckets_x27_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3987_; 
lean_inc(v_bkt_3963_);
v___x_3982_ = lean_box(0);
v_buckets_x27_3983_ = lean_array_uset(v_buckets_3945_, v___x_3962_, v___x_3982_);
v___x_3984_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3942_, v_b_3943_, v_bkt_3963_);
v___x_3985_ = lean_array_uset(v_buckets_x27_3983_, v___x_3962_, v___x_3984_);
if (v_isShared_3948_ == 0)
{
lean_ctor_set(v___x_3947_, 1, v___x_3985_);
v___x_3987_ = v___x_3947_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_size_3944_);
lean_ctor_set(v_reuseFailAlloc_3988_, 1, v___x_3985_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object* v_attrName_3992_, lean_object* v_ref_3993_){
_start:
{
lean_object* v___x_3995_; 
lean_inc(v_ref_3993_);
v___x_3995_ = l_Lean_Meta_Grind_mkExtension(v_ref_3993_);
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_object* v_a_3996_; uint8_t v___x_3997_; uint8_t v___x_3998_; lean_object* v___x_3999_; 
v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
lean_inc_n(v_a_3996_, 2);
lean_dec_ref_known(v___x_3995_, 1);
v___x_3997_ = 0;
v___x_3998_ = 1;
lean_inc(v_ref_3993_);
lean_inc(v_attrName_3992_);
v___x_3999_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3992_, v___x_3997_, v___x_3998_, v_a_3996_, v_ref_3993_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v___x_4000_; 
lean_dec_ref_known(v___x_3999_, 1);
lean_inc(v_ref_3993_);
lean_inc(v_a_3996_);
lean_inc(v_attrName_3992_);
v___x_4000_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3992_, v___x_3997_, v___x_3997_, v_a_3996_, v_ref_3993_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v___x_4001_; 
lean_dec_ref_known(v___x_4000_, 1);
lean_inc(v_ref_3993_);
lean_inc(v_a_3996_);
lean_inc(v_attrName_3992_);
v___x_4001_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3992_, v___x_3998_, v___x_3998_, v_a_3996_, v_ref_3993_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v___x_4002_; 
lean_dec_ref_known(v___x_4001_, 1);
lean_inc(v_a_3996_);
lean_inc(v_attrName_3992_);
v___x_4002_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3992_, v___x_3998_, v___x_3997_, v_a_3996_, v_ref_3993_);
if (lean_obj_tag(v___x_4002_) == 0)
{
lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4013_; 
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4013_ == 0)
{
lean_object* v_unused_4014_; 
v_unused_4014_ = lean_ctor_get(v___x_4002_, 0);
lean_dec(v_unused_4014_);
v___x_4004_ = v___x_4002_;
v_isShared_4005_ = v_isSharedCheck_4013_;
goto v_resetjp_4003_;
}
else
{
lean_dec(v___x_4002_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4013_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4011_; 
v___x_4006_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_4007_ = lean_st_ref_take(v___x_4006_);
lean_inc(v_a_3996_);
v___x_4008_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v___x_4007_, v_attrName_3992_, v_a_3996_);
v___x_4009_ = lean_st_ref_put(v___x_4006_, v___x_4008_);
if (v_isShared_4005_ == 0)
{
lean_ctor_set(v___x_4004_, 0, v_a_3996_);
v___x_4011_ = v___x_4004_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_3996_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
else
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
lean_dec(v_a_3996_);
lean_dec(v_attrName_3992_);
v_a_4015_ = lean_ctor_get(v___x_4002_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4017_ = v___x_4002_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_4002_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4015_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
}
else
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4030_; 
lean_dec(v_a_3996_);
lean_dec(v_ref_3993_);
lean_dec(v_attrName_3992_);
v_a_4023_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4025_ = v___x_4001_;
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_4001_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4028_; 
if (v_isShared_4026_ == 0)
{
v___x_4028_ = v___x_4025_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_a_4023_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
}
else
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4038_; 
lean_dec(v_a_3996_);
lean_dec(v_ref_3993_);
lean_dec(v_attrName_3992_);
v_a_4031_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4033_ = v___x_4000_;
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_4000_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4036_; 
if (v_isShared_4034_ == 0)
{
v___x_4036_ = v___x_4033_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4031_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
}
else
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4046_; 
lean_dec(v_a_3996_);
lean_dec(v_ref_3993_);
lean_dec(v_attrName_3992_);
v_a_4039_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4041_ = v___x_3999_;
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v___x_3999_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4044_; 
if (v_isShared_4042_ == 0)
{
v___x_4044_ = v___x_4041_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_a_4039_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
}
else
{
lean_dec(v_ref_3993_);
lean_dec(v_attrName_3992_);
return v___x_3995_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object* v_attrName_4047_, lean_object* v_ref_4048_, lean_object* v_a_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Lean_Meta_Grind_registerAttr(v_attrName_4047_, v_ref_4048_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object* v_00_u03b2_4051_, lean_object* v_m_4052_, lean_object* v_a_4053_, lean_object* v_b_4054_){
_start:
{
lean_object* v___x_4055_; 
v___x_4055_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v_m_4052_, v_a_4053_, v_b_4054_);
return v___x_4055_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object* v_00_u03b2_4056_, lean_object* v_a_4057_, lean_object* v_x_4058_){
_start:
{
uint8_t v___x_4059_; 
v___x_4059_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4057_, v_x_4058_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4060_, lean_object* v_a_4061_, lean_object* v_x_4062_){
_start:
{
uint8_t v_res_4063_; lean_object* v_r_4064_; 
v_res_4063_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(v_00_u03b2_4060_, v_a_4061_, v_x_4062_);
lean_dec(v_x_4062_);
lean_dec(v_a_4061_);
v_r_4064_ = lean_box(v_res_4063_);
return v_r_4064_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object* v_00_u03b2_4065_, lean_object* v_data_4066_){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_data_4066_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object* v_00_u03b2_4068_, lean_object* v_a_4069_, lean_object* v_b_4070_, lean_object* v_x_4071_){
_start:
{
lean_object* v___x_4072_; 
v___x_4072_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4069_, v_b_4070_, v_x_4071_);
return v___x_4072_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4073_, lean_object* v_i_4074_, lean_object* v_source_4075_, lean_object* v_target_4076_){
_start:
{
lean_object* v___x_4077_; 
v___x_4077_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v_i_4074_, v_source_4075_, v_target_4076_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4078_, lean_object* v_x_4079_, lean_object* v_x_4080_){
_start:
{
lean_object* v___x_4081_; 
v___x_4081_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_4079_, v_x_4080_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4088_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_4089_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_));
v___x_4090_ = l_Lean_Meta_Grind_registerAttr(v___x_4088_, v___x_4089_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object* v_a_4091_){
_start:
{
lean_object* v_res_4092_; 
v_res_4092_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4103_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_4104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_4105_ = l_Lean_Meta_Grind_registerAttr(v___x_4103_, v___x_4104_);
return v___x_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2____boxed(lean_object* v_a_4106_){
_start:
{
lean_object* v_res_4107_; 
v_res_4107_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object* v_declName_4108_, lean_object* v_a_4109_){
_start:
{
lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v_env_4113_; lean_object* v___x_4114_; lean_object* v_ext_4115_; lean_object* v_toEnvExtension_4116_; lean_object* v_asyncMode_4117_; lean_object* v___x_4118_; lean_object* v_casesTypes_4119_; uint8_t v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4111_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4112_ = lean_st_ref_get(v_a_4109_);
v_env_4113_ = lean_ctor_get(v___x_4112_, 0);
lean_inc_ref(v_env_4113_);
lean_dec(v___x_4112_);
v___x_4114_ = l_Lean_Meta_Grind_grindExt;
v_ext_4115_ = lean_ctor_get(v___x_4114_, 1);
v_toEnvExtension_4116_ = lean_ctor_get(v_ext_4115_, 0);
v_asyncMode_4117_ = lean_ctor_get(v_toEnvExtension_4116_, 2);
v___x_4118_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4111_, v___x_4114_, v_env_4113_, v_asyncMode_4117_);
v_casesTypes_4119_ = lean_ctor_get(v___x_4118_, 0);
lean_inc_ref(v_casesTypes_4119_);
lean_dec(v___x_4118_);
v___x_4120_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_casesTypes_4119_, v_declName_4108_);
lean_dec_ref(v_casesTypes_4119_);
v___x_4121_ = lean_box(v___x_4120_);
v___x_4122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4121_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object* v_declName_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_){
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4123_, v_a_4124_);
lean_dec(v_a_4124_);
lean_dec(v_declName_4123_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object* v_declName_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_){
_start:
{
lean_object* v___x_4131_; 
v___x_4131_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4127_, v_a_4129_);
return v___x_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object* v_declName_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_){
_start:
{
lean_object* v_res_4136_; 
v_res_4136_ = l_Lean_Meta_Grind_isGlobalSplit(v_declName_4132_, v_a_4133_, v_a_4134_);
lean_dec(v_a_4134_);
lean_dec_ref(v_a_4133_);
lean_dec(v_declName_4132_);
return v_res_4136_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Injective(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ExtAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Homo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
