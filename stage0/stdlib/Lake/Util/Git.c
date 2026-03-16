// Lean compiler output
// Module: Lake.Util.Git
// Imports: public import Init.Data.ToString public import Lake.Util.Proc import Init.Data.String.TakeDrop import Init.Data.String.Search
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*);
lean_object* l_Lake_captureProc_x3f(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_testProc(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* l_Lake_captureProc_x27(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static const lean_string_object l_Lake_Git_defaultRemote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "origin"};
static const lean_object* l_Lake_Git_defaultRemote___closed__0 = (const lean_object*)&l_Lake_Git_defaultRemote___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Git_defaultRemote = (const lean_object*)&l_Lake_Git_defaultRemote___closed__0_value;
static const lean_string_object l_Lake_Git_upstreamBranch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "master"};
static const lean_object* l_Lake_Git_upstreamBranch___closed__0 = (const lean_object*)&l_Lake_Git_upstreamBranch___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Git_upstreamBranch = (const lean_object*)&l_Lake_Git_upstreamBranch___closed__0_value;
static const lean_string_object l_Lake_Git_filterUrl_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ".git"};
static const lean_object* l_Lake_Git_filterUrl_x3f___closed__0 = (const lean_object*)&l_Lake_Git_filterUrl_x3f___closed__0_value;
static lean_once_cell_t l_Lake_Git_filterUrl_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Git_filterUrl_x3f___closed__1;
static const lean_string_object l_Lake_Git_filterUrl_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "git"};
static const lean_object* l_Lake_Git_filterUrl_x3f___closed__2 = (const lean_object*)&l_Lake_Git_filterUrl_x3f___closed__2_value;
static lean_once_cell_t l_Lake_Git_filterUrl_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Git_filterUrl_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instCoeFilePathGitRepo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instCoeFilePathGitRepo___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instCoeFilePathGitRepo___closed__0 = (const lean_object*)&l_Lake_instCoeFilePathGitRepo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeFilePathGitRepo = (const lean_object*)&l_Lake_instCoeFilePathGitRepo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToStringGitRepo = (const lean_object*)&l_Lake_instCoeFilePathGitRepo___closed__0_value;
static const lean_string_object l_Lake_GitRepo_cwd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_GitRepo_cwd___closed__0 = (const lean_object*)&l_Lake_GitRepo_cwd___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRepo_cwd = (const lean_object*)&l_Lake_GitRepo_cwd___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_GitRepo_dirExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_GitRepo_captureGit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_GitRepo_captureGit___closed__0 = (const lean_object*)&l_Lake_GitRepo_captureGit___closed__0_value;
static const lean_array_object l_Lake_GitRepo_captureGit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_GitRepo_captureGit___closed__1 = (const lean_object*)&l_Lake_GitRepo_captureGit___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_GitRepo_testGit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_clone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clone"};
static const lean_object* l_Lake_GitRepo_clone___closed__0 = (const lean_object*)&l_Lake_GitRepo_clone___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_clone___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_clone___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_quietInit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "init"};
static const lean_object* l_Lake_GitRepo_quietInit___closed__0 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__0_value;
static const lean_string_object l_Lake_GitRepo_quietInit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-q"};
static const lean_object* l_Lake_GitRepo_quietInit___closed__1 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__1_value;
static const lean_array_object l_Lake_GitRepo_quietInit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_quietInit___closed__0_value),((lean_object*)&l_Lake_GitRepo_quietInit___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_quietInit___closed__2 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_insideWorkTree___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rev-parse"};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__0 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__0_value;
static const lean_string_object l_Lake_GitRepo_insideWorkTree___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "--is-inside-work-tree"};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__1 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__1_value;
static const lean_array_object l_Lake_GitRepo_insideWorkTree___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__0_value),((lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__2 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__2_value;
LEAN_EXPORT uint8_t l_Lake_GitRepo_insideWorkTree(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_insideWorkTree___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_fetch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "fetch"};
static const lean_object* l_Lake_GitRepo_fetch___closed__0 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__0_value;
static const lean_string_object l_Lake_GitRepo_fetch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--tags"};
static const lean_object* l_Lake_GitRepo_fetch___closed__1 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__1_value;
static const lean_string_object l_Lake_GitRepo_fetch___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "--force"};
static const lean_object* l_Lake_GitRepo_fetch___closed__2 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__2_value;
static lean_once_cell_t l_Lake_GitRepo_fetch___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetch___closed__3;
static lean_once_cell_t l_Lake_GitRepo_fetch___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetch___closed__4;
static lean_once_cell_t l_Lake_GitRepo_fetch___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetch___closed__5;
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_checkoutBranch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "checkout"};
static const lean_object* l_Lake_GitRepo_checkoutBranch___closed__0 = (const lean_object*)&l_Lake_GitRepo_checkoutBranch___closed__0_value;
static const lean_string_object l_Lake_GitRepo_checkoutBranch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-B"};
static const lean_object* l_Lake_GitRepo_checkoutBranch___closed__1 = (const lean_object*)&l_Lake_GitRepo_checkoutBranch___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_checkoutBranch___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__2;
static lean_once_cell_t l_Lake_GitRepo_checkoutBranch___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_checkoutDetach___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--detach"};
static const lean_object* l_Lake_GitRepo_checkoutDetach___closed__0 = (const lean_object*)&l_Lake_GitRepo_checkoutDetach___closed__0_value;
static const lean_string_object l_Lake_GitRepo_checkoutDetach___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "--"};
static const lean_object* l_Lake_GitRepo_checkoutDetach___closed__1 = (const lean_object*)&l_Lake_GitRepo_checkoutDetach___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_checkoutDetach___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__2;
static lean_once_cell_t l_Lake_GitRepo_checkoutDetach___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_resolveRevision_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--verify"};
static const lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_resolveRevision_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_resolveRevision_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "--end-of-options"};
static const lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_resolveRevision_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_resolveRevision_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_resolveRevision_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__3;
static lean_once_cell_t l_Lake_GitRepo_resolveRevision_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_resolveRevision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = ": revision not found '"};
static const lean_object* l_Lake_GitRepo_resolveRevision___closed__0 = (const lean_object*)&l_Lake_GitRepo_resolveRevision___closed__0_value;
static const lean_string_object l_Lake_GitRepo_resolveRevision___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lake_GitRepo_resolveRevision___closed__1 = (const lean_object*)&l_Lake_GitRepo_resolveRevision___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getHeadRevision_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Lake_GitRepo_getHeadRevision_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_getHeadRevision_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getHeadRevision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 114, .m_capacity = 114, .m_length = 113, .m_data = ": could not resolve 'HEAD' to a commit; the repository may be corrupt, so you may need to remove it and try again"};
static const lean_object* l_Lake_GitRepo_getHeadRevision___closed__0 = (const lean_object*)&l_Lake_GitRepo_getHeadRevision___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getHeadRevisions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rev-list"};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__0 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__0_value;
static const lean_array_object l_Lake_GitRepo_getHeadRevisions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__0_value),((lean_object*)&l_Lake_GitRepo_getHeadRevision_x3f___closed__0_value)}};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__1 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__1_value;
static const lean_string_object l_Lake_GitRepo_getHeadRevisions___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-n"};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__2 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__2_value;
static lean_once_cell_t l_Lake_GitRepo_getHeadRevisions___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_getHeadRevisions___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_resolveRemoteRevision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Lake_GitRepo_resolveRemoteRevision___closed__0 = (const lean_object*)&l_Lake_GitRepo_resolveRemoteRevision___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_branchExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "show-ref"};
static const lean_object* l_Lake_GitRepo_branchExists___closed__0 = (const lean_object*)&l_Lake_GitRepo_branchExists___closed__0_value;
static const lean_string_object l_Lake_GitRepo_branchExists___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "refs/heads/"};
static const lean_object* l_Lake_GitRepo_branchExists___closed__1 = (const lean_object*)&l_Lake_GitRepo_branchExists___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_branchExists___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_branchExists___closed__2;
static lean_once_cell_t l_Lake_GitRepo_branchExists___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_branchExists___closed__3;
LEAN_EXPORT uint8_t l_Lake_GitRepo_branchExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_revisionExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "^{commit}"};
static const lean_object* l_Lake_GitRepo_revisionExists___closed__0 = (const lean_object*)&l_Lake_GitRepo_revisionExists___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_revisionExists___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_revisionExists___closed__1;
static lean_once_cell_t l_Lake_GitRepo_revisionExists___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_revisionExists___closed__2;
LEAN_EXPORT uint8_t l_Lake_GitRepo_revisionExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getTags___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "tag"};
static const lean_object* l_Lake_GitRepo_getTags___closed__0 = (const lean_object*)&l_Lake_GitRepo_getTags___closed__0_value;
static const lean_array_object l_Lake_GitRepo_getTags___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lake_GitRepo_getTags___closed__0_value)}};
static const lean_object* l_Lake_GitRepo_getTags___closed__1 = (const lean_object*)&l_Lake_GitRepo_getTags___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_findTag_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "describe"};
static const lean_object* l_Lake_GitRepo_findTag_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_findTag_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_findTag_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "--exact-match"};
static const lean_object* l_Lake_GitRepo_findTag_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_findTag_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_findTag_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_findTag_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__3;
static lean_once_cell_t l_Lake_GitRepo_findTag_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getRemoteUrl_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "remote"};
static const lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_getRemoteUrl_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_getRemoteUrl_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "get-url"};
static const lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_getRemoteUrl_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_getRemoteUrl_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_getRemoteUrl_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_hasNoDiff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "diff"};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__0 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__0_value;
static const lean_string_object l_Lake_GitRepo_hasNoDiff___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "--exit-code"};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__1 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__1_value;
static const lean_array_object l_Lake_GitRepo_hasNoDiff___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__0_value),((lean_object*)&l_Lake_GitRepo_getHeadRevision_x3f___closed__0_value),((lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__2 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__2_value;
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasNoDiff(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasDiff(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lake_Git_filterUrl_x3f___closed__1(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__0));
v___x_7_ = lean_string_utf8_byte_size(v___x_6_);
return v___x_7_;
}
}
static lean_object* _init_l_Lake_Git_filterUrl_x3f___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_10_ = lean_string_utf8_byte_size(v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object* v_url_11_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_27_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_28_ = lean_string_utf8_byte_size(v_url_11_);
v___x_29_ = lean_obj_once(&l_Lake_Git_filterUrl_x3f___closed__3, &l_Lake_Git_filterUrl_x3f___closed__3_once, _init_l_Lake_Git_filterUrl_x3f___closed__3);
v___x_30_ = lean_nat_dec_le(v___x_29_, v___x_28_);
if (v___x_30_ == 0)
{
goto v___jp_12_;
}
else
{
lean_object* v___x_31_; uint8_t v___x_32_; 
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_string_memcmp(v_url_11_, v___x_27_, v___x_31_, v___x_31_, v___x_29_);
if (v___x_32_ == 0)
{
goto v___jp_12_;
}
else
{
lean_object* v___x_33_; 
lean_dec_ref(v_url_11_);
v___x_33_ = lean_box(0);
return v___x_33_;
}
}
v___jp_12_:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_13_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__0));
v___x_14_ = lean_string_utf8_byte_size(v_url_11_);
v___x_15_ = lean_obj_once(&l_Lake_Git_filterUrl_x3f___closed__1, &l_Lake_Git_filterUrl_x3f___closed__1_once, _init_l_Lake_Git_filterUrl_x3f___closed__1);
v___x_16_ = lean_nat_dec_le(v___x_15_, v___x_14_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; 
v___x_17_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_17_, 0, v_url_11_);
return v___x_17_;
}
else
{
lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = lean_nat_sub(v___x_14_, v___x_15_);
v___x_20_ = lean_string_memcmp(v_url_11_, v___x_13_, v___x_19_, v___x_18_, v___x_15_);
lean_dec(v___x_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v_url_11_);
return v___x_21_;
}
else
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_22_ = lean_unsigned_to_nat(4u);
lean_inc_ref(v_url_11_);
v___x_23_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_23_, 0, v_url_11_);
lean_ctor_set(v___x_23_, 1, v___x_18_);
lean_ctor_set(v___x_23_, 2, v___x_14_);
v___x_24_ = l_String_Slice_Pos_prevn(v___x_23_, v___x_14_, v___x_22_);
lean_dec_ref(v___x_23_);
v___x_25_ = lean_string_utf8_extract(v_url_11_, v___x_18_, v___x_24_);
lean_dec(v___x_24_);
lean_dec_ref(v_url_11_);
v___x_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0(lean_object* v_s_34_, lean_object* v_curr_35_){
_start:
{
lean_object* v_str_36_; lean_object* v_startInclusive_37_; lean_object* v_endExclusive_38_; lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___y_48_; lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v_str_36_ = lean_ctor_get(v_s_34_, 0);
v_startInclusive_37_ = lean_ctor_get(v_s_34_, 1);
v_endExclusive_38_ = lean_ctor_get(v_s_34_, 2);
v___x_39_ = lean_nat_add(v_startInclusive_37_, v_curr_35_);
lean_inc(v_endExclusive_38_);
lean_inc(v___x_39_);
lean_inc_ref(v_str_36_);
v___x_40_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_40_, 0, v_str_36_);
lean_ctor_set(v___x_40_, 1, v___x_39_);
lean_ctor_set(v___x_40_, 2, v_endExclusive_38_);
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = lean_nat_sub(v_endExclusive_38_, v___x_39_);
v___x_51_ = lean_nat_dec_eq(v___x_49_, v___x_50_);
lean_dec(v___x_50_);
if (v___x_51_ == 0)
{
uint32_t v___x_52_; uint8_t v___y_54_; uint32_t v___x_59_; uint8_t v___x_60_; 
v___x_52_ = lean_string_utf8_get_fast(v_str_36_, v___x_39_);
v___x_59_ = 48;
v___x_60_ = lean_uint32_dec_le(v___x_59_, v___x_52_);
if (v___x_60_ == 0)
{
v___y_54_ = v___x_60_;
goto v___jp_53_;
}
else
{
uint32_t v___x_61_; uint8_t v___x_62_; 
v___x_61_ = 57;
v___x_62_ = lean_uint32_dec_le(v___x_52_, v___x_61_);
v___y_54_ = v___x_62_;
goto v___jp_53_;
}
v___jp_53_:
{
if (v___y_54_ == 0)
{
uint32_t v___x_55_; uint8_t v___x_56_; 
v___x_55_ = 97;
v___x_56_ = lean_uint32_dec_le(v___x_55_, v___x_52_);
if (v___x_56_ == 0)
{
v___y_48_ = v___x_56_;
goto v___jp_47_;
}
else
{
uint32_t v___x_57_; uint8_t v___x_58_; 
v___x_57_ = 102;
v___x_58_ = lean_uint32_dec_le(v___x_52_, v___x_57_);
v___y_48_ = v___x_58_;
goto v___jp_47_;
}
}
else
{
goto v___jp_41_;
}
}
}
else
{
lean_dec(v___x_39_);
lean_dec(v_curr_35_);
return v___x_40_;
}
v___jp_41_:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_42_ = lean_string_utf8_next_fast(v_str_36_, v___x_39_);
v___x_43_ = lean_nat_sub(v___x_42_, v___x_39_);
lean_dec(v___x_39_);
v___x_44_ = lean_nat_add(v_curr_35_, v___x_43_);
lean_dec(v___x_43_);
v___x_45_ = lean_nat_dec_lt(v_curr_35_, v___x_44_);
lean_dec(v_curr_35_);
if (v___x_45_ == 0)
{
lean_dec(v___x_44_);
return v___x_40_;
}
else
{
lean_dec_ref(v___x_40_);
v_curr_35_ = v___x_44_;
goto _start;
}
}
v___jp_47_:
{
if (v___y_48_ == 0)
{
lean_dec(v___x_39_);
lean_dec(v_curr_35_);
return v___x_40_;
}
else
{
goto v___jp_41_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0___boxed(lean_object* v_s_63_, lean_object* v_curr_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0(v_s_63_, v_curr_64_);
lean_dec_ref(v_s_63_);
return v_res_65_;
}
}
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object* v_rev_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_67_ = lean_string_length(v_rev_66_);
v___x_68_ = lean_unsigned_to_nat(40u);
v___x_69_ = lean_nat_dec_eq(v___x_67_, v___x_68_);
if (v___x_69_ == 0)
{
lean_dec_ref(v_rev_66_);
return v___x_69_;
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v_startInclusive_74_; lean_object* v_endExclusive_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = lean_string_utf8_byte_size(v_rev_66_);
v___x_72_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_72_, 0, v_rev_66_);
lean_ctor_set(v___x_72_, 1, v___x_70_);
lean_ctor_set(v___x_72_, 2, v___x_71_);
v___x_73_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0(v___x_72_, v___x_70_);
lean_dec_ref(v___x_72_);
v_startInclusive_74_ = lean_ctor_get(v___x_73_, 1);
lean_inc(v_startInclusive_74_);
v_endExclusive_75_ = lean_ctor_get(v___x_73_, 2);
lean_inc(v_endExclusive_75_);
lean_dec_ref(v___x_73_);
v___x_76_ = lean_nat_sub(v_endExclusive_75_, v_startInclusive_74_);
lean_dec(v_startInclusive_74_);
lean_dec(v_endExclusive_75_);
v___x_77_ = lean_nat_dec_eq(v___x_76_, v___x_70_);
lean_dec(v___x_76_);
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object* v_rev_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_Lake_Git_isFullObjectName(v_rev_78_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0(lean_object* v_x_81_){
_start:
{
lean_inc_ref(v_x_81_);
return v_x_81_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0___boxed(lean_object* v_x_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lake_instCoeFilePathGitRepo___lam__0(v_x_82_);
lean_dec_ref(v_x_82_);
return v_res_83_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_dirExists(lean_object* v_repo_89_){
_start:
{
uint8_t v___x_91_; 
v___x_91_ = l_System_FilePath_isDir(v_repo_89_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object* v_repo_92_, lean_object* v_a_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_Lake_GitRepo_dirExists(v_repo_92_);
lean_dec_ref(v_repo_92_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit(lean_object* v_args_100_, lean_object* v_repo_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_104_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_105_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_106_, 0, v_repo_101_);
v___x_107_ = lean_unsigned_to_nat(0u);
v___x_108_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_109_ = 1;
v___x_110_ = 0;
v___x_111_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_111_, 0, v___x_104_);
lean_ctor_set(v___x_111_, 1, v___x_105_);
lean_ctor_set(v___x_111_, 2, v_args_100_);
lean_ctor_set(v___x_111_, 3, v___x_106_);
lean_ctor_set(v___x_111_, 4, v___x_108_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*5, v___x_109_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*5 + 1, v___x_110_);
v___x_112_ = l_Lake_captureProc_x27(v___x_111_, v_a_102_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_129_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
v_a_114_ = lean_ctor_get(v___x_112_, 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_129_ == 0)
{
v___x_116_ = v___x_112_;
v_isShared_117_ = v_isSharedCheck_129_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_inc(v_a_113_);
lean_dec(v___x_112_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_129_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v_stdout_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v_str_122_; lean_object* v_startInclusive_123_; lean_object* v_endExclusive_124_; lean_object* v___x_125_; lean_object* v___x_127_; 
v_stdout_118_ = lean_ctor_get(v_a_113_, 0);
lean_inc_ref(v_stdout_118_);
lean_dec(v_a_113_);
v___x_119_ = lean_string_utf8_byte_size(v_stdout_118_);
v___x_120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_120_, 0, v_stdout_118_);
lean_ctor_set(v___x_120_, 1, v___x_107_);
lean_ctor_set(v___x_120_, 2, v___x_119_);
v___x_121_ = l_String_Slice_trimAscii(v___x_120_);
lean_dec_ref(v___x_120_);
v_str_122_ = lean_ctor_get(v___x_121_, 0);
lean_inc_ref(v_str_122_);
v_startInclusive_123_ = lean_ctor_get(v___x_121_, 1);
lean_inc(v_startInclusive_123_);
v_endExclusive_124_ = lean_ctor_get(v___x_121_, 2);
lean_inc(v_endExclusive_124_);
lean_dec_ref(v___x_121_);
v___x_125_ = lean_string_utf8_extract(v_str_122_, v_startInclusive_123_, v_endExclusive_124_);
lean_dec(v_endExclusive_124_);
lean_dec(v_startInclusive_123_);
lean_dec_ref(v_str_122_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 0, v___x_125_);
v___x_127_ = v___x_116_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_a_114_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
else
{
lean_object* v_a_130_; lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
v_a_130_ = lean_ctor_get(v___x_112_, 0);
v_a_131_ = lean_ctor_get(v___x_112_, 1);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_112_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_inc(v_a_130_);
lean_dec(v___x_112_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_130_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_a_131_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit___boxed(lean_object* v_args_139_, lean_object* v_repo_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lake_GitRepo_captureGit(v_args_139_, v_repo_140_, v_a_141_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object* v_args_144_, lean_object* v_repo_145_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; uint8_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_147_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_148_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_149_, 0, v_repo_145_);
v___x_150_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_151_ = 1;
v___x_152_ = 0;
v___x_153_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_153_, 0, v___x_147_);
lean_ctor_set(v___x_153_, 1, v___x_148_);
lean_ctor_set(v___x_153_, 2, v_args_144_);
lean_ctor_set(v___x_153_, 3, v___x_149_);
lean_ctor_set(v___x_153_, 4, v___x_150_);
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*5, v___x_151_);
lean_ctor_set_uint8(v___x_153_, sizeof(void*)*5 + 1, v___x_152_);
v___x_154_ = l_Lake_captureProc_x3f(v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f___boxed(lean_object* v_args_155_, lean_object* v_repo_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lake_GitRepo_captureGit_x3f(v_args_155_, v_repo_156_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object* v_args_159_, lean_object* v_repo_160_, lean_object* v_a_161_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_163_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_164_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_165_, 0, v_repo_160_);
v___x_166_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_167_ = 1;
v___x_168_ = 0;
v___x_169_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_169_, 0, v___x_163_);
lean_ctor_set(v___x_169_, 1, v___x_164_);
lean_ctor_set(v___x_169_, 2, v_args_159_);
lean_ctor_set(v___x_169_, 3, v___x_165_);
lean_ctor_set(v___x_169_, 4, v___x_166_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*5, v___x_167_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*5 + 1, v___x_168_);
v___x_170_ = l_Lake_proc(v___x_169_, v___x_167_, v_a_161_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit___boxed(lean_object* v_args_171_, lean_object* v_repo_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lake_GitRepo_execGit(v_args_171_, v_repo_172_, v_a_173_);
return v_res_175_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_testGit(lean_object* v_args_176_, lean_object* v_repo_177_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; uint8_t v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_179_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_180_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_181_, 0, v_repo_177_);
v___x_182_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_183_ = 1;
v___x_184_ = 0;
v___x_185_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_185_, 0, v___x_179_);
lean_ctor_set(v___x_185_, 1, v___x_180_);
lean_ctor_set(v___x_185_, 2, v_args_176_);
lean_ctor_set(v___x_185_, 3, v___x_181_);
lean_ctor_set(v___x_185_, 4, v___x_182_);
lean_ctor_set_uint8(v___x_185_, sizeof(void*)*5, v___x_183_);
lean_ctor_set_uint8(v___x_185_, sizeof(void*)*5 + 1, v___x_184_);
v___x_186_ = l_Lake_testProc(v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit___boxed(lean_object* v_args_187_, lean_object* v_repo_188_, lean_object* v_a_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l_Lake_GitRepo_testGit(v_args_187_, v_repo_188_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
static lean_object* _init_l_Lake_GitRepo_clone___closed__1(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_193_ = ((lean_object*)(l_Lake_GitRepo_clone___closed__0));
v___x_194_ = lean_unsigned_to_nat(3u);
v___x_195_ = lean_mk_empty_array_with_capacity(v___x_194_);
v___x_196_ = lean_array_push(v___x_195_, v___x_193_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object* v_url_197_, lean_object* v_repo_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_201_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_202_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_203_ = lean_obj_once(&l_Lake_GitRepo_clone___closed__1, &l_Lake_GitRepo_clone___closed__1_once, _init_l_Lake_GitRepo_clone___closed__1);
v___x_204_ = lean_array_push(v___x_203_, v_url_197_);
v___x_205_ = lean_array_push(v___x_204_, v_repo_198_);
v___x_206_ = lean_box(0);
v___x_207_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_208_ = 1;
v___x_209_ = 0;
v___x_210_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_210_, 0, v___x_201_);
lean_ctor_set(v___x_210_, 1, v___x_202_);
lean_ctor_set(v___x_210_, 2, v___x_205_);
lean_ctor_set(v___x_210_, 3, v___x_206_);
lean_ctor_set(v___x_210_, 4, v___x_207_);
lean_ctor_set_uint8(v___x_210_, sizeof(void*)*5, v___x_208_);
lean_ctor_set_uint8(v___x_210_, sizeof(void*)*5 + 1, v___x_209_);
v___x_211_ = l_Lake_proc(v___x_210_, v___x_208_, v_a_199_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone___boxed(lean_object* v_url_212_, lean_object* v_repo_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lake_GitRepo_clone(v_url_212_, v_repo_213_, v_a_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object* v_repo_225_, lean_object* v_a_226_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; uint8_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_228_ = ((lean_object*)(l_Lake_GitRepo_quietInit___closed__2));
v___x_229_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_230_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v_repo_225_);
v___x_232_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_233_ = 1;
v___x_234_ = 0;
v___x_235_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_235_, 0, v___x_229_);
lean_ctor_set(v___x_235_, 1, v___x_230_);
lean_ctor_set(v___x_235_, 2, v___x_228_);
lean_ctor_set(v___x_235_, 3, v___x_231_);
lean_ctor_set(v___x_235_, 4, v___x_232_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*5, v___x_233_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*5 + 1, v___x_234_);
v___x_236_ = l_Lake_proc(v___x_235_, v___x_233_, v_a_226_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit___boxed(lean_object* v_repo_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lake_GitRepo_quietInit(v_repo_237_, v_a_238_);
return v_res_240_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_insideWorkTree(lean_object* v_repo_249_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; uint8_t v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_251_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__2));
v___x_252_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_253_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_254_, 0, v_repo_249_);
v___x_255_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_256_ = 1;
v___x_257_ = 0;
v___x_258_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_258_, 0, v___x_252_);
lean_ctor_set(v___x_258_, 1, v___x_253_);
lean_ctor_set(v___x_258_, 2, v___x_251_);
lean_ctor_set(v___x_258_, 3, v___x_254_);
lean_ctor_set(v___x_258_, 4, v___x_255_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*5, v___x_256_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*5 + 1, v___x_257_);
v___x_259_ = l_Lake_testProc(v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_insideWorkTree___boxed(lean_object* v_repo_260_, lean_object* v_a_261_){
_start:
{
uint8_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l_Lake_GitRepo_insideWorkTree(v_repo_260_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__3(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_267_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__0));
v___x_268_ = lean_unsigned_to_nat(4u);
v___x_269_ = lean_mk_empty_array_with_capacity(v___x_268_);
v___x_270_ = lean_array_push(v___x_269_, v___x_267_);
return v___x_270_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__4(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_272_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__3, &l_Lake_GitRepo_fetch___closed__3_once, _init_l_Lake_GitRepo_fetch___closed__3);
v___x_273_ = lean_array_push(v___x_272_, v___x_271_);
return v___x_273_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__5(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__2));
v___x_275_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__4, &l_Lake_GitRepo_fetch___closed__4_once, _init_l_Lake_GitRepo_fetch___closed__4);
v___x_276_ = lean_array_push(v___x_275_, v___x_274_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object* v_repo_277_, lean_object* v_remote_278_, lean_object* v_a_279_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; uint8_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_281_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__5, &l_Lake_GitRepo_fetch___closed__5_once, _init_l_Lake_GitRepo_fetch___closed__5);
v___x_282_ = lean_array_push(v___x_281_, v_remote_278_);
v___x_283_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_284_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v_repo_277_);
v___x_286_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_287_ = 1;
v___x_288_ = 0;
v___x_289_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_289_, 0, v___x_283_);
lean_ctor_set(v___x_289_, 1, v___x_284_);
lean_ctor_set(v___x_289_, 2, v___x_282_);
lean_ctor_set(v___x_289_, 3, v___x_285_);
lean_ctor_set(v___x_289_, 4, v___x_286_);
lean_ctor_set_uint8(v___x_289_, sizeof(void*)*5, v___x_287_);
lean_ctor_set_uint8(v___x_289_, sizeof(void*)*5 + 1, v___x_288_);
v___x_290_ = l_Lake_proc(v___x_289_, v___x_287_, v_a_279_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch___boxed(lean_object* v_repo_291_, lean_object* v_remote_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lake_GitRepo_fetch(v_repo_291_, v_remote_292_, v_a_293_);
return v_res_295_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__2(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_298_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__0));
v___x_299_ = lean_unsigned_to_nat(3u);
v___x_300_ = lean_mk_empty_array_with_capacity(v___x_299_);
v___x_301_ = lean_array_push(v___x_300_, v___x_298_);
return v___x_301_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__3(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_302_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__1));
v___x_303_ = lean_obj_once(&l_Lake_GitRepo_checkoutBranch___closed__2, &l_Lake_GitRepo_checkoutBranch___closed__2_once, _init_l_Lake_GitRepo_checkoutBranch___closed__2);
v___x_304_ = lean_array_push(v___x_303_, v___x_302_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object* v_branch_305_, lean_object* v_repo_306_, lean_object* v_a_307_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_309_ = lean_obj_once(&l_Lake_GitRepo_checkoutBranch___closed__3, &l_Lake_GitRepo_checkoutBranch___closed__3_once, _init_l_Lake_GitRepo_checkoutBranch___closed__3);
v___x_310_ = lean_array_push(v___x_309_, v_branch_305_);
v___x_311_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_312_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v_repo_306_);
v___x_314_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_315_ = 1;
v___x_316_ = 0;
v___x_317_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_317_, 0, v___x_311_);
lean_ctor_set(v___x_317_, 1, v___x_312_);
lean_ctor_set(v___x_317_, 2, v___x_310_);
lean_ctor_set(v___x_317_, 3, v___x_313_);
lean_ctor_set(v___x_317_, 4, v___x_314_);
lean_ctor_set_uint8(v___x_317_, sizeof(void*)*5, v___x_315_);
lean_ctor_set_uint8(v___x_317_, sizeof(void*)*5 + 1, v___x_316_);
v___x_318_ = l_Lake_proc(v___x_317_, v___x_315_, v_a_307_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch___boxed(lean_object* v_branch_319_, lean_object* v_repo_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lake_GitRepo_checkoutBranch(v_branch_319_, v_repo_320_, v_a_321_);
return v_res_323_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__2(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_326_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__0));
v___x_327_ = lean_unsigned_to_nat(4u);
v___x_328_ = lean_mk_empty_array_with_capacity(v___x_327_);
v___x_329_ = lean_array_push(v___x_328_, v___x_326_);
return v___x_329_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__3(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_330_ = ((lean_object*)(l_Lake_GitRepo_checkoutDetach___closed__0));
v___x_331_ = lean_obj_once(&l_Lake_GitRepo_checkoutDetach___closed__2, &l_Lake_GitRepo_checkoutDetach___closed__2_once, _init_l_Lake_GitRepo_checkoutDetach___closed__2);
v___x_332_ = lean_array_push(v___x_331_, v___x_330_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object* v_hash_333_, lean_object* v_repo_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; uint8_t v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_337_ = ((lean_object*)(l_Lake_GitRepo_checkoutDetach___closed__1));
v___x_338_ = lean_obj_once(&l_Lake_GitRepo_checkoutDetach___closed__3, &l_Lake_GitRepo_checkoutDetach___closed__3_once, _init_l_Lake_GitRepo_checkoutDetach___closed__3);
v___x_339_ = lean_array_push(v___x_338_, v_hash_333_);
v___x_340_ = lean_array_push(v___x_339_, v___x_337_);
v___x_341_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_342_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_343_, 0, v_repo_334_);
v___x_344_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_345_ = 1;
v___x_346_ = 0;
v___x_347_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_347_, 0, v___x_341_);
lean_ctor_set(v___x_347_, 1, v___x_342_);
lean_ctor_set(v___x_347_, 2, v___x_340_);
lean_ctor_set(v___x_347_, 3, v___x_343_);
lean_ctor_set(v___x_347_, 4, v___x_344_);
lean_ctor_set_uint8(v___x_347_, sizeof(void*)*5, v___x_345_);
lean_ctor_set_uint8(v___x_347_, sizeof(void*)*5 + 1, v___x_346_);
v___x_348_ = l_Lake_proc(v___x_347_, v___x_345_, v_a_335_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach___boxed(lean_object* v_hash_349_, lean_object* v_repo_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lake_GitRepo_checkoutDetach(v_hash_349_, v_repo_350_, v_a_351_);
return v_res_353_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_356_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__0));
v___x_357_ = lean_unsigned_to_nat(4u);
v___x_358_ = lean_mk_empty_array_with_capacity(v___x_357_);
v___x_359_ = lean_array_push(v___x_358_, v___x_356_);
return v___x_359_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_360_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_361_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__2, &l_Lake_GitRepo_resolveRevision_x3f___closed__2_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2);
v___x_362_ = lean_array_push(v___x_361_, v___x_360_);
return v___x_362_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__1));
v___x_364_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__3, &l_Lake_GitRepo_resolveRevision_x3f___closed__3_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3);
v___x_365_ = lean_array_push(v___x_364_, v___x_363_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object* v_rev_366_, lean_object* v_repo_367_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; uint8_t v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_369_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__4, &l_Lake_GitRepo_resolveRevision_x3f___closed__4_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4);
v___x_370_ = lean_array_push(v___x_369_, v_rev_366_);
v___x_371_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_372_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_373_, 0, v_repo_367_);
v___x_374_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_375_ = 1;
v___x_376_ = 0;
v___x_377_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_377_, 0, v___x_371_);
lean_ctor_set(v___x_377_, 1, v___x_372_);
lean_ctor_set(v___x_377_, 2, v___x_370_);
lean_ctor_set(v___x_377_, 3, v___x_373_);
lean_ctor_set(v___x_377_, 4, v___x_374_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*5, v___x_375_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*5 + 1, v___x_376_);
v___x_378_ = l_Lake_captureProc_x3f(v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f___boxed(lean_object* v_rev_379_, lean_object* v_repo_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_379_, v_repo_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision(lean_object* v_rev_385_, lean_object* v_repo_386_, lean_object* v_a_387_){
_start:
{
uint8_t v___x_389_; 
lean_inc_ref(v_rev_385_);
v___x_389_ = l_Lake_Git_isFullObjectName(v_rev_385_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; 
lean_inc_ref(v_repo_386_);
lean_inc_ref(v_rev_385_);
v___x_390_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_385_, v_repo_386_);
if (lean_obj_tag(v___x_390_) == 1)
{
lean_object* v_val_391_; lean_object* v___x_392_; 
lean_dec_ref(v_repo_386_);
lean_dec_ref(v_rev_385_);
v_val_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_val_391_);
lean_dec_ref(v___x_390_);
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v_val_391_);
lean_ctor_set(v___x_392_, 1, v_a_387_);
return v___x_392_;
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec(v___x_390_);
v___x_393_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__0));
v___x_394_ = lean_string_append(v_repo_386_, v___x_393_);
v___x_395_ = lean_string_append(v___x_394_, v_rev_385_);
lean_dec_ref(v_rev_385_);
v___x_396_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__1));
v___x_397_ = lean_string_append(v___x_395_, v___x_396_);
v___x_398_ = 3;
v___x_399_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_399_, 0, v___x_397_);
lean_ctor_set_uint8(v___x_399_, sizeof(void*)*1, v___x_398_);
v___x_400_ = lean_array_get_size(v_a_387_);
v___x_401_ = lean_array_push(v_a_387_, v___x_399_);
v___x_402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
return v___x_402_;
}
}
else
{
lean_object* v___x_403_; 
lean_dec_ref(v_repo_386_);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v_rev_385_);
lean_ctor_set(v___x_403_, 1, v_a_387_);
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision___boxed(lean_object* v_rev_404_, lean_object* v_repo_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lake_GitRepo_resolveRevision(v_rev_404_, v_repo_405_, v_a_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object* v_repo_410_){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevision_x3f___closed__0));
v___x_413_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_412_, v_repo_410_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f___boxed(lean_object* v_repo_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lake_GitRepo_getHeadRevision_x3f(v_repo_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object* v_repo_418_, lean_object* v_a_419_){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevision_x3f___closed__0));
lean_inc_ref(v_repo_418_);
v___x_422_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_421_, v_repo_418_);
if (lean_obj_tag(v___x_422_) == 1)
{
lean_object* v_val_423_; lean_object* v___x_424_; 
lean_dec_ref(v_repo_418_);
v_val_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_val_423_);
lean_dec_ref(v___x_422_);
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v_val_423_);
lean_ctor_set(v___x_424_, 1, v_a_419_);
return v___x_424_;
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec(v___x_422_);
v___x_425_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevision___closed__0));
v___x_426_ = lean_string_append(v_repo_418_, v___x_425_);
v___x_427_ = 3;
v___x_428_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*1, v___x_427_);
v___x_429_ = lean_array_get_size(v_a_419_);
v___x_430_ = lean_array_push(v_a_419_, v___x_428_);
v___x_431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_429_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
return v___x_431_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision___boxed(lean_object* v_repo_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lake_GitRepo_getHeadRevision(v_repo_432_, v_a_433_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(lean_object* v_s_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0));
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___boxed(lean_object* v_s_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v_s_440_);
lean_dec_ref(v_s_440_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(lean_object* v___x_442_, lean_object* v___x_443_, lean_object* v___x_444_, lean_object* v_a_445_, lean_object* v_b_446_){
_start:
{
lean_object* v_it_448_; lean_object* v_startInclusive_449_; lean_object* v_endExclusive_450_; 
if (lean_obj_tag(v_a_445_) == 0)
{
lean_object* v_currPos_455_; lean_object* v_searcher_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_482_; 
v_currPos_455_ = lean_ctor_get(v_a_445_, 0);
v_searcher_456_ = lean_ctor_get(v_a_445_, 1);
v_isSharedCheck_482_ = !lean_is_exclusive(v_a_445_);
if (v_isSharedCheck_482_ == 0)
{
v___x_458_ = v_a_445_;
v_isShared_459_ = v_isSharedCheck_482_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_searcher_456_);
lean_inc(v_currPos_455_);
lean_dec(v_a_445_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_482_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_startInclusive_460_; lean_object* v_endExclusive_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v_startInclusive_460_ = lean_ctor_get(v___x_443_, 1);
v_endExclusive_461_ = lean_ctor_get(v___x_443_, 2);
v___x_462_ = lean_nat_sub(v_endExclusive_461_, v_startInclusive_460_);
v___x_463_ = lean_nat_dec_eq(v_searcher_456_, v___x_462_);
lean_dec(v___x_462_);
if (v___x_463_ == 0)
{
uint32_t v___x_464_; uint32_t v___x_465_; uint8_t v___x_466_; 
v___x_464_ = 10;
v___x_465_ = lean_string_utf8_get_fast(v___x_442_, v_searcher_456_);
v___x_466_ = lean_uint32_dec_eq(v___x_465_, v___x_464_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_467_ = lean_string_utf8_next_fast(v___x_442_, v_searcher_456_);
lean_dec(v_searcher_456_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 1, v___x_467_);
v___x_469_ = v___x_458_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_currPos_455_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v___x_467_);
v___x_469_ = v_reuseFailAlloc_471_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
v_a_445_ = v___x_469_;
goto _start;
}
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v_slice_475_; lean_object* v_nextIt_477_; 
v___x_472_ = lean_string_utf8_next_fast(v___x_442_, v_searcher_456_);
v___x_473_ = lean_nat_sub(v___x_472_, v_searcher_456_);
v___x_474_ = lean_nat_add(v_searcher_456_, v___x_473_);
lean_dec(v___x_473_);
v_slice_475_ = l_String_Slice_subslice_x21(v___x_443_, v_currPos_455_, v_searcher_456_);
lean_inc(v___x_474_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 1, v___x_474_);
lean_ctor_set(v___x_458_, 0, v___x_474_);
v_nextIt_477_ = v___x_458_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v___x_474_);
v_nextIt_477_ = v_reuseFailAlloc_480_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v_startInclusive_478_; lean_object* v_endExclusive_479_; 
v_startInclusive_478_ = lean_ctor_get(v_slice_475_, 0);
lean_inc(v_startInclusive_478_);
v_endExclusive_479_ = lean_ctor_get(v_slice_475_, 1);
lean_inc(v_endExclusive_479_);
lean_dec_ref(v_slice_475_);
v_it_448_ = v_nextIt_477_;
v_startInclusive_449_ = v_startInclusive_478_;
v_endExclusive_450_ = v_endExclusive_479_;
goto v___jp_447_;
}
}
}
else
{
lean_object* v___x_481_; 
lean_del_object(v___x_458_);
lean_dec(v_searcher_456_);
v___x_481_ = lean_box(1);
lean_inc(v___x_444_);
v_it_448_ = v___x_481_;
v_startInclusive_449_ = v_currPos_455_;
v_endExclusive_450_ = v___x_444_;
goto v___jp_447_;
}
}
}
else
{
lean_dec(v___x_444_);
lean_dec_ref(v___x_442_);
return v_b_446_;
}
v___jp_447_:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
lean_inc_ref(v___x_442_);
v___x_451_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_451_, 0, v___x_442_);
lean_ctor_set(v___x_451_, 1, v_startInclusive_449_);
lean_ctor_set(v___x_451_, 2, v_endExclusive_450_);
v___x_452_ = l_String_Slice_toString(v___x_451_);
lean_dec_ref(v___x_451_);
v___x_453_ = lean_array_push(v_b_446_, v___x_452_);
v_a_445_ = v_it_448_;
v_b_446_ = v___x_453_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___boxed(lean_object* v___x_483_, lean_object* v___x_484_, lean_object* v___x_485_, lean_object* v_a_486_, lean_object* v_b_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_483_, v___x_484_, v___x_485_, v_a_486_, v_b_487_);
lean_dec_ref(v___x_484_);
return v_res_488_;
}
}
static lean_object* _init_l_Lake_GitRepo_getHeadRevisions___closed__3(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_497_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevisions___closed__2));
v___x_498_ = lean_unsigned_to_nat(2u);
v___x_499_ = lean_mk_empty_array_with_capacity(v___x_498_);
v___x_500_ = lean_array_push(v___x_499_, v___x_497_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions(lean_object* v_repo_501_, lean_object* v_n_502_, lean_object* v_a_503_){
_start:
{
lean_object* v___y_506_; lean_object* v_args_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v_args_552_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevisions___closed__1));
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_nat_dec_eq(v_n_502_, v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_555_ = l_Nat_reprFast(v_n_502_);
v___x_556_ = lean_obj_once(&l_Lake_GitRepo_getHeadRevisions___closed__3, &l_Lake_GitRepo_getHeadRevisions___closed__3_once, _init_l_Lake_GitRepo_getHeadRevisions___closed__3);
v___x_557_ = lean_array_push(v___x_556_, v___x_555_);
v___x_558_ = l_Array_append___redArg(v_args_552_, v___x_557_);
lean_dec_ref(v___x_557_);
v___y_506_ = v___x_558_;
goto v___jp_505_;
}
else
{
lean_dec(v_n_502_);
v___y_506_ = v_args_552_;
goto v___jp_505_;
}
v___jp_505_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; uint8_t v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_507_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_508_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_509_, 0, v_repo_501_);
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_512_ = 1;
v___x_513_ = 0;
v___x_514_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_514_, 0, v___x_507_);
lean_ctor_set(v___x_514_, 1, v___x_508_);
lean_ctor_set(v___x_514_, 2, v___y_506_);
lean_ctor_set(v___x_514_, 3, v___x_509_);
lean_ctor_set(v___x_514_, 4, v___x_511_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*5, v___x_512_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*5 + 1, v___x_513_);
v___x_515_ = l_Lake_captureProc_x27(v___x_514_, v_a_503_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_542_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
v_a_517_ = lean_ctor_get(v___x_515_, 1);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_542_ == 0)
{
v___x_519_ = v___x_515_;
v_isShared_520_ = v_isSharedCheck_542_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_inc(v_a_516_);
lean_dec(v___x_515_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_542_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v_stdout_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v_str_525_; lean_object* v_startInclusive_526_; lean_object* v_endExclusive_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_541_; 
v_stdout_521_ = lean_ctor_get(v_a_516_, 0);
lean_inc_ref(v_stdout_521_);
lean_dec(v_a_516_);
v___x_522_ = lean_string_utf8_byte_size(v_stdout_521_);
v___x_523_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_523_, 0, v_stdout_521_);
lean_ctor_set(v___x_523_, 1, v___x_510_);
lean_ctor_set(v___x_523_, 2, v___x_522_);
v___x_524_ = l_String_Slice_trimAscii(v___x_523_);
lean_dec_ref(v___x_523_);
v_str_525_ = lean_ctor_get(v___x_524_, 0);
v_startInclusive_526_ = lean_ctor_get(v___x_524_, 1);
v_endExclusive_527_ = lean_ctor_get(v___x_524_, 2);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_541_ == 0)
{
v___x_529_ = v___x_524_;
v_isShared_530_ = v_isSharedCheck_541_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_endExclusive_527_);
lean_inc(v_startInclusive_526_);
lean_inc(v_str_525_);
lean_dec(v___x_524_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_541_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_531_ = lean_string_utf8_extract(v_str_525_, v_startInclusive_526_, v_endExclusive_527_);
lean_dec(v_endExclusive_527_);
lean_dec(v_startInclusive_526_);
lean_dec_ref(v_str_525_);
v___x_532_ = lean_string_utf8_byte_size(v___x_531_);
lean_inc_ref(v___x_531_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 2, v___x_532_);
lean_ctor_set(v___x_529_, 1, v___x_510_);
lean_ctor_set(v___x_529_, 0, v___x_531_);
v___x_534_ = v___x_529_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_540_, 2, v___x_532_);
v___x_534_ = v_reuseFailAlloc_540_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_535_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v___x_534_);
v___x_536_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_531_, v___x_534_, v___x_532_, v___x_535_, v___x_511_);
lean_dec_ref(v___x_534_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v___x_536_);
v___x_538_ = v___x_519_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v_a_517_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
else
{
lean_object* v_a_543_; lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
v_a_543_ = lean_ctor_get(v___x_515_, 0);
v_a_544_ = lean_ctor_get(v___x_515_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_515_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_inc(v_a_543_);
lean_dec(v___x_515_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
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
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_543_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions___boxed(lean_object* v_repo_559_, lean_object* v_n_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lake_GitRepo_getHeadRevisions(v_repo_559_, v_n_560_, v_a_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(lean_object* v___x_564_, lean_object* v___x_565_, lean_object* v___x_566_, lean_object* v_inst_567_, lean_object* v_R_568_, lean_object* v_a_569_, lean_object* v_b_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_564_, v___x_565_, v___x_566_, v_a_569_, v_b_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___boxed(lean_object* v___x_572_, lean_object* v___x_573_, lean_object* v___x_574_, lean_object* v_inst_575_, lean_object* v_R_576_, lean_object* v_a_577_, lean_object* v_b_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(v___x_572_, v___x_573_, v___x_574_, v_inst_575_, v_R_576_, v_a_577_, v_b_578_);
lean_dec_ref(v___x_573_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object* v_rev_581_, lean_object* v_remote_582_, lean_object* v_repo_583_, lean_object* v_a_584_){
_start:
{
uint8_t v___x_586_; 
lean_inc_ref(v_rev_581_);
v___x_586_ = l_Lake_Git_isFullObjectName(v_rev_581_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_587_ = ((lean_object*)(l_Lake_GitRepo_resolveRemoteRevision___closed__0));
v___x_588_ = lean_string_append(v_remote_582_, v___x_587_);
v___x_589_ = lean_string_append(v___x_588_, v_rev_581_);
lean_inc_ref(v_repo_583_);
v___x_590_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_589_, v_repo_583_);
if (lean_obj_tag(v___x_590_) == 1)
{
lean_object* v_val_591_; lean_object* v___x_592_; 
lean_dec_ref(v_repo_583_);
lean_dec_ref(v_rev_581_);
v_val_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_val_591_);
lean_dec_ref(v___x_590_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v_val_591_);
lean_ctor_set(v___x_592_, 1, v_a_584_);
return v___x_592_;
}
else
{
lean_object* v___x_593_; 
lean_dec(v___x_590_);
lean_inc_ref(v_repo_583_);
lean_inc_ref(v_rev_581_);
v___x_593_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_581_, v_repo_583_);
if (lean_obj_tag(v___x_593_) == 1)
{
lean_object* v_val_594_; lean_object* v___x_595_; 
lean_dec_ref(v_repo_583_);
lean_dec_ref(v_rev_581_);
v_val_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_val_594_);
lean_dec_ref(v___x_593_);
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v_val_594_);
lean_ctor_set(v___x_595_, 1, v_a_584_);
return v___x_595_;
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
lean_dec(v___x_593_);
v___x_596_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__0));
v___x_597_ = lean_string_append(v_repo_583_, v___x_596_);
v___x_598_ = lean_string_append(v___x_597_, v_rev_581_);
lean_dec_ref(v_rev_581_);
v___x_599_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__1));
v___x_600_ = lean_string_append(v___x_598_, v___x_599_);
v___x_601_ = 3;
v___x_602_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set_uint8(v___x_602_, sizeof(void*)*1, v___x_601_);
v___x_603_ = lean_array_get_size(v_a_584_);
v___x_604_ = lean_array_push(v_a_584_, v___x_602_);
v___x_605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
return v___x_605_;
}
}
}
else
{
lean_object* v___x_606_; 
lean_dec_ref(v_repo_583_);
lean_dec_ref(v_remote_582_);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v_rev_581_);
lean_ctor_set(v___x_606_, 1, v_a_584_);
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___boxed(lean_object* v_rev_607_, lean_object* v_remote_608_, lean_object* v_repo_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lake_GitRepo_resolveRemoteRevision(v_rev_607_, v_remote_608_, v_repo_609_, v_a_610_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object* v_repo_613_, lean_object* v_rev_x3f_614_, lean_object* v_remote_615_, lean_object* v_a_616_){
_start:
{
lean_object* v___x_618_; 
lean_inc_ref(v_remote_615_);
lean_inc_ref(v_repo_613_);
v___x_618_ = l_Lake_GitRepo_fetch(v_repo_613_, v_remote_615_, v_a_616_);
if (lean_obj_tag(v___x_618_) == 0)
{
if (lean_obj_tag(v_rev_x3f_614_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_a_619_ = lean_ctor_get(v___x_618_, 1);
lean_inc(v_a_619_);
lean_dec_ref(v___x_618_);
v___x_620_ = ((lean_object*)(l_Lake_Git_upstreamBranch___closed__0));
v___x_621_ = l_Lake_GitRepo_resolveRemoteRevision(v___x_620_, v_remote_615_, v_repo_613_, v_a_619_);
return v___x_621_;
}
else
{
lean_object* v_a_622_; lean_object* v_val_623_; lean_object* v___x_624_; 
v_a_622_ = lean_ctor_get(v___x_618_, 1);
lean_inc(v_a_622_);
lean_dec_ref(v___x_618_);
v_val_623_ = lean_ctor_get(v_rev_x3f_614_, 0);
lean_inc(v_val_623_);
lean_dec_ref(v_rev_x3f_614_);
v___x_624_ = l_Lake_GitRepo_resolveRemoteRevision(v_val_623_, v_remote_615_, v_repo_613_, v_a_622_);
return v___x_624_;
}
}
else
{
lean_object* v_a_625_; lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec_ref(v_remote_615_);
lean_dec(v_rev_x3f_614_);
lean_dec_ref(v_repo_613_);
v_a_625_ = lean_ctor_get(v___x_618_, 0);
v_a_626_ = lean_ctor_get(v___x_618_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_618_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_inc(v_a_625_);
lean_dec(v___x_618_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_625_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision___boxed(lean_object* v_repo_634_, lean_object* v_rev_x3f_635_, lean_object* v_remote_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lake_GitRepo_findRemoteRevision(v_repo_634_, v_rev_x3f_635_, v_remote_636_, v_a_637_);
return v_res_639_;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__2(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_642_ = ((lean_object*)(l_Lake_GitRepo_branchExists___closed__0));
v___x_643_ = lean_unsigned_to_nat(3u);
v___x_644_ = lean_mk_empty_array_with_capacity(v___x_643_);
v___x_645_ = lean_array_push(v___x_644_, v___x_642_);
return v___x_645_;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__3(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_647_ = lean_obj_once(&l_Lake_GitRepo_branchExists___closed__2, &l_Lake_GitRepo_branchExists___closed__2_once, _init_l_Lake_GitRepo_branchExists___closed__2);
v___x_648_ = lean_array_push(v___x_647_, v___x_646_);
return v___x_648_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_branchExists(lean_object* v_rev_649_, lean_object* v_repo_650_){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; uint8_t v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_652_ = ((lean_object*)(l_Lake_GitRepo_branchExists___closed__1));
v___x_653_ = lean_string_append(v___x_652_, v_rev_649_);
v___x_654_ = lean_obj_once(&l_Lake_GitRepo_branchExists___closed__3, &l_Lake_GitRepo_branchExists___closed__3_once, _init_l_Lake_GitRepo_branchExists___closed__3);
v___x_655_ = lean_array_push(v___x_654_, v___x_653_);
v___x_656_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_657_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_658_, 0, v_repo_650_);
v___x_659_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_660_ = 1;
v___x_661_ = 0;
v___x_662_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_662_, 0, v___x_656_);
lean_ctor_set(v___x_662_, 1, v___x_657_);
lean_ctor_set(v___x_662_, 2, v___x_655_);
lean_ctor_set(v___x_662_, 3, v___x_658_);
lean_ctor_set(v___x_662_, 4, v___x_659_);
lean_ctor_set_uint8(v___x_662_, sizeof(void*)*5, v___x_660_);
lean_ctor_set_uint8(v___x_662_, sizeof(void*)*5 + 1, v___x_661_);
v___x_663_ = l_Lake_testProc(v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object* v_rev_664_, lean_object* v_repo_665_, lean_object* v_a_666_){
_start:
{
uint8_t v_res_667_; lean_object* v_r_668_; 
v_res_667_ = l_Lake_GitRepo_branchExists(v_rev_664_, v_repo_665_);
lean_dec_ref(v_rev_664_);
v_r_668_ = lean_box(v_res_667_);
return v_r_668_;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__1(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_670_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__0));
v___x_671_ = lean_unsigned_to_nat(3u);
v___x_672_ = lean_mk_empty_array_with_capacity(v___x_671_);
v___x_673_ = lean_array_push(v___x_672_, v___x_670_);
return v___x_673_;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__2(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_675_ = lean_obj_once(&l_Lake_GitRepo_revisionExists___closed__1, &l_Lake_GitRepo_revisionExists___closed__1_once, _init_l_Lake_GitRepo_revisionExists___closed__1);
v___x_676_ = lean_array_push(v___x_675_, v___x_674_);
return v___x_676_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_revisionExists(lean_object* v_rev_677_, lean_object* v_repo_678_){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; uint8_t v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_680_ = ((lean_object*)(l_Lake_GitRepo_revisionExists___closed__0));
v___x_681_ = lean_string_append(v_rev_677_, v___x_680_);
v___x_682_ = lean_obj_once(&l_Lake_GitRepo_revisionExists___closed__2, &l_Lake_GitRepo_revisionExists___closed__2_once, _init_l_Lake_GitRepo_revisionExists___closed__2);
v___x_683_ = lean_array_push(v___x_682_, v___x_681_);
v___x_684_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_685_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_686_, 0, v_repo_678_);
v___x_687_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_688_ = 1;
v___x_689_ = 0;
v___x_690_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_690_, 0, v___x_684_);
lean_ctor_set(v___x_690_, 1, v___x_685_);
lean_ctor_set(v___x_690_, 2, v___x_683_);
lean_ctor_set(v___x_690_, 3, v___x_686_);
lean_ctor_set(v___x_690_, 4, v___x_687_);
lean_ctor_set_uint8(v___x_690_, sizeof(void*)*5, v___x_688_);
lean_ctor_set_uint8(v___x_690_, sizeof(void*)*5 + 1, v___x_689_);
v___x_691_ = l_Lake_testProc(v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists___boxed(lean_object* v_rev_692_, lean_object* v_repo_693_, lean_object* v_a_694_){
_start:
{
uint8_t v_res_695_; lean_object* v_r_696_; 
v_res_695_ = l_Lake_GitRepo_revisionExists(v_rev_692_, v_repo_693_);
v_r_696_ = lean_box(v_res_695_);
return v_r_696_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags(lean_object* v_repo_702_){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; uint8_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_704_ = ((lean_object*)(l_Lake_GitRepo_getTags___closed__1));
v___x_705_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_706_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_707_, 0, v_repo_702_);
v___x_708_ = lean_unsigned_to_nat(0u);
v___x_709_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_710_ = 1;
v___x_711_ = 0;
v___x_712_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_712_, 0, v___x_705_);
lean_ctor_set(v___x_712_, 1, v___x_706_);
lean_ctor_set(v___x_712_, 2, v___x_704_);
lean_ctor_set(v___x_712_, 3, v___x_707_);
lean_ctor_set(v___x_712_, 4, v___x_709_);
lean_ctor_set_uint8(v___x_712_, sizeof(void*)*5, v___x_710_);
lean_ctor_set_uint8(v___x_712_, sizeof(void*)*5 + 1, v___x_711_);
v___x_713_ = l_Lake_captureProc_x3f(v___x_712_);
if (lean_obj_tag(v___x_713_) == 1)
{
lean_object* v_val_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v_val_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_val_714_);
lean_dec_ref(v___x_713_);
v___x_715_ = lean_string_utf8_byte_size(v_val_714_);
lean_inc(v_val_714_);
v___x_716_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_716_, 0, v_val_714_);
lean_ctor_set(v___x_716_, 1, v___x_708_);
lean_ctor_set(v___x_716_, 2, v___x_715_);
v___x_717_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v___x_716_);
v___x_718_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v_val_714_, v___x_716_, v___x_715_, v___x_717_, v___x_709_);
lean_dec_ref(v___x_716_);
v___x_719_ = lean_array_to_list(v___x_718_);
return v___x_719_;
}
else
{
lean_object* v___x_720_; 
lean_dec(v___x_713_);
v___x_720_ = lean_box(0);
return v___x_720_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags___boxed(lean_object* v_repo_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lake_GitRepo_getTags(v_repo_721_);
return v_res_723_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__2(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_726_ = ((lean_object*)(l_Lake_GitRepo_findTag_x3f___closed__0));
v___x_727_ = lean_unsigned_to_nat(4u);
v___x_728_ = lean_mk_empty_array_with_capacity(v___x_727_);
v___x_729_ = lean_array_push(v___x_728_, v___x_726_);
return v___x_729_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__3(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_730_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_731_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__2, &l_Lake_GitRepo_findTag_x3f___closed__2_once, _init_l_Lake_GitRepo_findTag_x3f___closed__2);
v___x_732_ = lean_array_push(v___x_731_, v___x_730_);
return v___x_732_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__4(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_733_ = ((lean_object*)(l_Lake_GitRepo_findTag_x3f___closed__1));
v___x_734_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__3, &l_Lake_GitRepo_findTag_x3f___closed__3_once, _init_l_Lake_GitRepo_findTag_x3f___closed__3);
v___x_735_ = lean_array_push(v___x_734_, v___x_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object* v_rev_736_, lean_object* v_repo_737_){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; uint8_t v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_739_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__4, &l_Lake_GitRepo_findTag_x3f___closed__4_once, _init_l_Lake_GitRepo_findTag_x3f___closed__4);
v___x_740_ = lean_array_push(v___x_739_, v_rev_736_);
v___x_741_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_742_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_743_, 0, v_repo_737_);
v___x_744_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_745_ = 1;
v___x_746_ = 0;
v___x_747_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_747_, 0, v___x_741_);
lean_ctor_set(v___x_747_, 1, v___x_742_);
lean_ctor_set(v___x_747_, 2, v___x_740_);
lean_ctor_set(v___x_747_, 3, v___x_743_);
lean_ctor_set(v___x_747_, 4, v___x_744_);
lean_ctor_set_uint8(v___x_747_, sizeof(void*)*5, v___x_745_);
lean_ctor_set_uint8(v___x_747_, sizeof(void*)*5 + 1, v___x_746_);
v___x_748_ = l_Lake_captureProc_x3f(v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f___boxed(lean_object* v_rev_749_, lean_object* v_repo_750_, lean_object* v_a_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lake_GitRepo_findTag_x3f(v_rev_749_, v_repo_750_);
return v_res_752_;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_755_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__0));
v___x_756_ = lean_unsigned_to_nat(3u);
v___x_757_ = lean_mk_empty_array_with_capacity(v___x_756_);
v___x_758_ = lean_array_push(v___x_757_, v___x_755_);
return v___x_758_;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_759_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__1));
v___x_760_ = lean_obj_once(&l_Lake_GitRepo_getRemoteUrl_x3f___closed__2, &l_Lake_GitRepo_getRemoteUrl_x3f___closed__2_once, _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2);
v___x_761_ = lean_array_push(v___x_760_, v___x_759_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object* v_remote_762_, lean_object* v_repo_763_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; uint8_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_765_ = lean_obj_once(&l_Lake_GitRepo_getRemoteUrl_x3f___closed__3, &l_Lake_GitRepo_getRemoteUrl_x3f___closed__3_once, _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3);
v___x_766_ = lean_array_push(v___x_765_, v_remote_762_);
v___x_767_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_768_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_769_, 0, v_repo_763_);
v___x_770_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_771_ = 1;
v___x_772_ = 0;
v___x_773_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_773_, 0, v___x_767_);
lean_ctor_set(v___x_773_, 1, v___x_768_);
lean_ctor_set(v___x_773_, 2, v___x_766_);
lean_ctor_set(v___x_773_, 3, v___x_769_);
lean_ctor_set(v___x_773_, 4, v___x_770_);
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*5, v___x_771_);
lean_ctor_set_uint8(v___x_773_, sizeof(void*)*5 + 1, v___x_772_);
v___x_774_ = l_Lake_captureProc_x3f(v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___boxed(lean_object* v_remote_775_, lean_object* v_repo_776_, lean_object* v_a_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lake_GitRepo_getRemoteUrl_x3f(v_remote_775_, v_repo_776_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object* v_remote_779_, lean_object* v_repo_780_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lake_GitRepo_getRemoteUrl_x3f(v_remote_779_, v_repo_780_);
if (lean_obj_tag(v___x_782_) == 0)
{
return v___x_782_;
}
else
{
lean_object* v_val_783_; lean_object* v___x_784_; 
v_val_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_val_783_);
lean_dec_ref(v___x_782_);
v___x_784_ = l_Lake_Git_filterUrl_x3f(v_val_783_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f___boxed(lean_object* v_remote_785_, lean_object* v_repo_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v_remote_785_, v_repo_786_);
return v_res_788_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasNoDiff(lean_object* v_repo_799_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; uint8_t v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_801_ = ((lean_object*)(l_Lake_GitRepo_hasNoDiff___closed__2));
v___x_802_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_803_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_804_, 0, v_repo_799_);
v___x_805_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_806_ = 1;
v___x_807_ = 0;
v___x_808_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_808_, 0, v___x_802_);
lean_ctor_set(v___x_808_, 1, v___x_803_);
lean_ctor_set(v___x_808_, 2, v___x_801_);
lean_ctor_set(v___x_808_, 3, v___x_804_);
lean_ctor_set(v___x_808_, 4, v___x_805_);
lean_ctor_set_uint8(v___x_808_, sizeof(void*)*5, v___x_806_);
lean_ctor_set_uint8(v___x_808_, sizeof(void*)*5 + 1, v___x_807_);
v___x_809_ = l_Lake_testProc(v___x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff___boxed(lean_object* v_repo_810_, lean_object* v_a_811_){
_start:
{
uint8_t v_res_812_; lean_object* v_r_813_; 
v_res_812_ = l_Lake_GitRepo_hasNoDiff(v_repo_810_);
v_r_813_ = lean_box(v_res_812_);
return v_r_813_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasDiff(lean_object* v_repo_814_){
_start:
{
uint8_t v___x_816_; 
v___x_816_ = l_Lake_GitRepo_hasNoDiff(v_repo_814_);
if (v___x_816_ == 0)
{
uint8_t v___x_817_; 
v___x_817_ = 1;
return v___x_817_;
}
else
{
uint8_t v___x_818_; 
v___x_818_ = 0;
return v___x_818_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff___boxed(lean_object* v_repo_819_, lean_object* v_a_820_){
_start:
{
uint8_t v_res_821_; lean_object* v_r_822_; 
v_res_821_ = l_Lake_GitRepo_hasDiff(v_repo_819_);
v_r_822_ = lean_box(v_res_821_);
return v_r_822_;
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Git(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Git(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Git(builtin);
}
#ifdef __cplusplus
}
#endif
