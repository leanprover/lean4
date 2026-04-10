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
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lake_Git_isFullObjectName_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lake_Git_isFullObjectName_spec__0___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Lake_GitRepo_clean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clean"};
static const lean_object* l_Lake_GitRepo_clean___closed__0 = (const lean_object*)&l_Lake_GitRepo_clean___closed__0_value;
static const lean_string_object l_Lake_GitRepo_clean___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "-xf"};
static const lean_object* l_Lake_GitRepo_clean___closed__1 = (const lean_object*)&l_Lake_GitRepo_clean___closed__1_value;
static const lean_array_object l_Lake_GitRepo_clean___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_clean___closed__0_value),((lean_object*)&l_Lake_GitRepo_clean___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_clean___closed__2 = (const lean_object*)&l_Lake_GitRepo_clean___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lake_Git_isFullObjectName_spec__0(lean_object* v_s_34_, lean_object* v_pos_35_){
_start:
{
lean_object* v_str_36_; lean_object* v_startInclusive_37_; lean_object* v_endExclusive_38_; lean_object* v___x_39_; uint8_t v___y_47_; lean_object* v___x_48_; lean_object* v___x_49_; uint8_t v___x_50_; 
v_str_36_ = lean_ctor_get(v_s_34_, 0);
v_startInclusive_37_ = lean_ctor_get(v_s_34_, 1);
v_endExclusive_38_ = lean_ctor_get(v_s_34_, 2);
v___x_39_ = lean_nat_add(v_startInclusive_37_, v_pos_35_);
v___x_48_ = lean_unsigned_to_nat(0u);
v___x_49_ = lean_nat_sub(v_endExclusive_38_, v___x_39_);
v___x_50_ = lean_nat_dec_eq(v___x_48_, v___x_49_);
lean_dec(v___x_49_);
if (v___x_50_ == 0)
{
uint32_t v___x_51_; uint8_t v___y_53_; uint32_t v___x_58_; uint8_t v___x_59_; 
v___x_51_ = lean_string_utf8_get_fast(v_str_36_, v___x_39_);
v___x_58_ = 48;
v___x_59_ = lean_uint32_dec_le(v___x_58_, v___x_51_);
if (v___x_59_ == 0)
{
v___y_53_ = v___x_59_;
goto v___jp_52_;
}
else
{
uint32_t v___x_60_; uint8_t v___x_61_; 
v___x_60_ = 57;
v___x_61_ = lean_uint32_dec_le(v___x_51_, v___x_60_);
v___y_53_ = v___x_61_;
goto v___jp_52_;
}
v___jp_52_:
{
if (v___y_53_ == 0)
{
uint32_t v___x_54_; uint8_t v___x_55_; 
v___x_54_ = 97;
v___x_55_ = lean_uint32_dec_le(v___x_54_, v___x_51_);
if (v___x_55_ == 0)
{
v___y_47_ = v___x_55_;
goto v___jp_46_;
}
else
{
uint32_t v___x_56_; uint8_t v___x_57_; 
v___x_56_ = 102;
v___x_57_ = lean_uint32_dec_le(v___x_51_, v___x_56_);
v___y_47_ = v___x_57_;
goto v___jp_46_;
}
}
else
{
goto v___jp_40_;
}
}
}
else
{
lean_dec(v___x_39_);
return v_pos_35_;
}
v___jp_40_:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_41_ = lean_string_utf8_next_fast(v_str_36_, v___x_39_);
v___x_42_ = lean_nat_sub(v___x_41_, v___x_39_);
lean_dec(v___x_39_);
v___x_43_ = lean_nat_add(v_pos_35_, v___x_42_);
lean_dec(v___x_42_);
v___x_44_ = lean_nat_dec_lt(v_pos_35_, v___x_43_);
if (v___x_44_ == 0)
{
lean_dec(v___x_43_);
return v_pos_35_;
}
else
{
lean_dec(v_pos_35_);
v_pos_35_ = v___x_43_;
goto _start;
}
}
v___jp_46_:
{
if (v___y_47_ == 0)
{
lean_dec(v___x_39_);
return v_pos_35_;
}
else
{
goto v___jp_40_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Lake_Git_isFullObjectName_spec__0___boxed(lean_object* v_s_62_, lean_object* v_pos_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_String_Slice_Pos_skipWhile___at___00Lake_Git_isFullObjectName_spec__0(v_s_62_, v_pos_63_);
lean_dec_ref(v_s_62_);
return v_res_64_;
}
}
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object* v_rev_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_66_ = lean_string_length(v_rev_65_);
v___x_67_ = lean_unsigned_to_nat(40u);
v___x_68_ = lean_nat_dec_eq(v___x_66_, v___x_67_);
if (v___x_68_ == 0)
{
lean_dec_ref(v_rev_65_);
return v___x_68_;
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_string_utf8_byte_size(v_rev_65_);
v___x_71_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_71_, 0, v_rev_65_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_70_);
v___x_72_ = l_String_Slice_Pos_skipWhile___at___00Lake_Git_isFullObjectName_spec__0(v___x_71_, v___x_69_);
lean_dec_ref(v___x_71_);
v___x_73_ = lean_nat_dec_eq(v___x_72_, v___x_70_);
lean_dec(v___x_72_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object* v_rev_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_Lake_Git_isFullObjectName(v_rev_74_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0(lean_object* v_x_77_){
_start:
{
lean_inc_ref(v_x_77_);
return v_x_77_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0___boxed(lean_object* v_x_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lake_instCoeFilePathGitRepo___lam__0(v_x_78_);
lean_dec_ref(v_x_78_);
return v_res_79_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_dirExists(lean_object* v_repo_85_){
_start:
{
uint8_t v___x_87_; 
v___x_87_ = l_System_FilePath_isDir(v_repo_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object* v_repo_88_, lean_object* v_a_89_){
_start:
{
uint8_t v_res_90_; lean_object* v_r_91_; 
v_res_90_ = l_Lake_GitRepo_dirExists(v_repo_88_);
lean_dec_ref(v_repo_88_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit(lean_object* v_args_96_, lean_object* v_repo_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; uint8_t v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_100_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_101_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_102_, 0, v_repo_97_);
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_105_ = 1;
v___x_106_ = 0;
v___x_107_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_107_, 0, v___x_100_);
lean_ctor_set(v___x_107_, 1, v___x_101_);
lean_ctor_set(v___x_107_, 2, v_args_96_);
lean_ctor_set(v___x_107_, 3, v___x_102_);
lean_ctor_set(v___x_107_, 4, v___x_104_);
lean_ctor_set_uint8(v___x_107_, sizeof(void*)*5, v___x_105_);
lean_ctor_set_uint8(v___x_107_, sizeof(void*)*5 + 1, v___x_106_);
v___x_108_ = l_Lake_captureProc_x27(v___x_107_, v_a_98_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_125_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
v_a_110_ = lean_ctor_get(v___x_108_, 1);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_125_ == 0)
{
v___x_112_ = v___x_108_;
v_isShared_113_ = v_isSharedCheck_125_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_inc(v_a_109_);
lean_dec(v___x_108_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_125_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v_stdout_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v_str_118_; lean_object* v_startInclusive_119_; lean_object* v_endExclusive_120_; lean_object* v___x_121_; lean_object* v___x_123_; 
v_stdout_114_ = lean_ctor_get(v_a_109_, 0);
lean_inc_ref(v_stdout_114_);
lean_dec(v_a_109_);
v___x_115_ = lean_string_utf8_byte_size(v_stdout_114_);
v___x_116_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_116_, 0, v_stdout_114_);
lean_ctor_set(v___x_116_, 1, v___x_103_);
lean_ctor_set(v___x_116_, 2, v___x_115_);
v___x_117_ = l_String_Slice_trimAscii(v___x_116_);
v_str_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc_ref(v_str_118_);
v_startInclusive_119_ = lean_ctor_get(v___x_117_, 1);
lean_inc(v_startInclusive_119_);
v_endExclusive_120_ = lean_ctor_get(v___x_117_, 2);
lean_inc(v_endExclusive_120_);
lean_dec_ref(v___x_117_);
v___x_121_ = lean_string_utf8_extract(v_str_118_, v_startInclusive_119_, v_endExclusive_120_);
lean_dec(v_endExclusive_120_);
lean_dec(v_startInclusive_119_);
lean_dec_ref(v_str_118_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v___x_121_);
v___x_123_ = v___x_112_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v_a_110_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
else
{
lean_object* v_a_126_; lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_134_; 
v_a_126_ = lean_ctor_get(v___x_108_, 0);
v_a_127_ = lean_ctor_get(v___x_108_, 1);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_134_ == 0)
{
v___x_129_ = v___x_108_;
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_inc(v_a_126_);
lean_dec(v___x_108_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_126_);
lean_ctor_set(v_reuseFailAlloc_133_, 1, v_a_127_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit___boxed(lean_object* v_args_135_, lean_object* v_repo_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lake_GitRepo_captureGit(v_args_135_, v_repo_136_, v_a_137_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object* v_args_140_, lean_object* v_repo_141_){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; uint8_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_143_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_144_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_145_, 0, v_repo_141_);
v___x_146_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_147_ = 1;
v___x_148_ = 0;
v___x_149_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_149_, 0, v___x_143_);
lean_ctor_set(v___x_149_, 1, v___x_144_);
lean_ctor_set(v___x_149_, 2, v_args_140_);
lean_ctor_set(v___x_149_, 3, v___x_145_);
lean_ctor_set(v___x_149_, 4, v___x_146_);
lean_ctor_set_uint8(v___x_149_, sizeof(void*)*5, v___x_147_);
lean_ctor_set_uint8(v___x_149_, sizeof(void*)*5 + 1, v___x_148_);
v___x_150_ = l_Lake_captureProc_x3f(v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f___boxed(lean_object* v_args_151_, lean_object* v_repo_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lake_GitRepo_captureGit_x3f(v_args_151_, v_repo_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object* v_args_155_, lean_object* v_repo_156_, lean_object* v_a_157_){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; uint8_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_159_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_160_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_161_, 0, v_repo_156_);
v___x_162_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_163_ = 1;
v___x_164_ = 0;
v___x_165_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_165_, 0, v___x_159_);
lean_ctor_set(v___x_165_, 1, v___x_160_);
lean_ctor_set(v___x_165_, 2, v_args_155_);
lean_ctor_set(v___x_165_, 3, v___x_161_);
lean_ctor_set(v___x_165_, 4, v___x_162_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*5, v___x_163_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*5 + 1, v___x_164_);
v___x_166_ = l_Lake_proc(v___x_165_, v___x_163_, v_a_157_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit___boxed(lean_object* v_args_167_, lean_object* v_repo_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lake_GitRepo_execGit(v_args_167_, v_repo_168_, v_a_169_);
return v_res_171_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_testGit(lean_object* v_args_172_, lean_object* v_repo_173_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; uint8_t v___x_179_; uint8_t v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_175_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_176_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_177_, 0, v_repo_173_);
v___x_178_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_179_ = 1;
v___x_180_ = 0;
v___x_181_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_181_, 0, v___x_175_);
lean_ctor_set(v___x_181_, 1, v___x_176_);
lean_ctor_set(v___x_181_, 2, v_args_172_);
lean_ctor_set(v___x_181_, 3, v___x_177_);
lean_ctor_set(v___x_181_, 4, v___x_178_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*5, v___x_179_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*5 + 1, v___x_180_);
v___x_182_ = l_Lake_testProc(v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit___boxed(lean_object* v_args_183_, lean_object* v_repo_184_, lean_object* v_a_185_){
_start:
{
uint8_t v_res_186_; lean_object* v_r_187_; 
v_res_186_ = l_Lake_GitRepo_testGit(v_args_183_, v_repo_184_);
v_r_187_ = lean_box(v_res_186_);
return v_r_187_;
}
}
static lean_object* _init_l_Lake_GitRepo_clone___closed__1(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_189_ = ((lean_object*)(l_Lake_GitRepo_clone___closed__0));
v___x_190_ = lean_unsigned_to_nat(3u);
v___x_191_ = lean_mk_empty_array_with_capacity(v___x_190_);
v___x_192_ = lean_array_push(v___x_191_, v___x_189_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object* v_url_193_, lean_object* v_repo_194_, lean_object* v_a_195_){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; uint8_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_197_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_198_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_199_ = lean_obj_once(&l_Lake_GitRepo_clone___closed__1, &l_Lake_GitRepo_clone___closed__1_once, _init_l_Lake_GitRepo_clone___closed__1);
v___x_200_ = lean_array_push(v___x_199_, v_url_193_);
v___x_201_ = lean_array_push(v___x_200_, v_repo_194_);
v___x_202_ = lean_box(0);
v___x_203_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_204_ = 1;
v___x_205_ = 0;
v___x_206_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_206_, 0, v___x_197_);
lean_ctor_set(v___x_206_, 1, v___x_198_);
lean_ctor_set(v___x_206_, 2, v___x_201_);
lean_ctor_set(v___x_206_, 3, v___x_202_);
lean_ctor_set(v___x_206_, 4, v___x_203_);
lean_ctor_set_uint8(v___x_206_, sizeof(void*)*5, v___x_204_);
lean_ctor_set_uint8(v___x_206_, sizeof(void*)*5 + 1, v___x_205_);
v___x_207_ = l_Lake_proc(v___x_206_, v___x_204_, v_a_195_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone___boxed(lean_object* v_url_208_, lean_object* v_repo_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lake_GitRepo_clone(v_url_208_, v_repo_209_, v_a_210_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object* v_repo_221_, lean_object* v_a_222_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; uint8_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_224_ = ((lean_object*)(l_Lake_GitRepo_quietInit___closed__2));
v___x_225_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_226_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_227_, 0, v_repo_221_);
v___x_228_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_229_ = 1;
v___x_230_ = 0;
v___x_231_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_231_, 0, v___x_225_);
lean_ctor_set(v___x_231_, 1, v___x_226_);
lean_ctor_set(v___x_231_, 2, v___x_224_);
lean_ctor_set(v___x_231_, 3, v___x_227_);
lean_ctor_set(v___x_231_, 4, v___x_228_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*5, v___x_229_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*5 + 1, v___x_230_);
v___x_232_ = l_Lake_proc(v___x_231_, v___x_229_, v_a_222_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit___boxed(lean_object* v_repo_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lake_GitRepo_quietInit(v_repo_233_, v_a_234_);
return v_res_236_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_insideWorkTree(lean_object* v_repo_245_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; uint8_t v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_247_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__2));
v___x_248_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_249_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_250_, 0, v_repo_245_);
v___x_251_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_252_ = 1;
v___x_253_ = 0;
v___x_254_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_254_, 0, v___x_248_);
lean_ctor_set(v___x_254_, 1, v___x_249_);
lean_ctor_set(v___x_254_, 2, v___x_247_);
lean_ctor_set(v___x_254_, 3, v___x_250_);
lean_ctor_set(v___x_254_, 4, v___x_251_);
lean_ctor_set_uint8(v___x_254_, sizeof(void*)*5, v___x_252_);
lean_ctor_set_uint8(v___x_254_, sizeof(void*)*5 + 1, v___x_253_);
v___x_255_ = l_Lake_testProc(v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_insideWorkTree___boxed(lean_object* v_repo_256_, lean_object* v_a_257_){
_start:
{
uint8_t v_res_258_; lean_object* v_r_259_; 
v_res_258_ = l_Lake_GitRepo_insideWorkTree(v_repo_256_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__3(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_263_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__0));
v___x_264_ = lean_unsigned_to_nat(4u);
v___x_265_ = lean_mk_empty_array_with_capacity(v___x_264_);
v___x_266_ = lean_array_push(v___x_265_, v___x_263_);
return v___x_266_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__4(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_268_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__3, &l_Lake_GitRepo_fetch___closed__3_once, _init_l_Lake_GitRepo_fetch___closed__3);
v___x_269_ = lean_array_push(v___x_268_, v___x_267_);
return v___x_269_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__5(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__2));
v___x_271_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__4, &l_Lake_GitRepo_fetch___closed__4_once, _init_l_Lake_GitRepo_fetch___closed__4);
v___x_272_ = lean_array_push(v___x_271_, v___x_270_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object* v_repo_273_, lean_object* v_remote_274_, lean_object* v_a_275_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; uint8_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_277_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__5, &l_Lake_GitRepo_fetch___closed__5_once, _init_l_Lake_GitRepo_fetch___closed__5);
v___x_278_ = lean_array_push(v___x_277_, v_remote_274_);
v___x_279_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_280_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_281_, 0, v_repo_273_);
v___x_282_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_283_ = 1;
v___x_284_ = 0;
v___x_285_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_285_, 0, v___x_279_);
lean_ctor_set(v___x_285_, 1, v___x_280_);
lean_ctor_set(v___x_285_, 2, v___x_278_);
lean_ctor_set(v___x_285_, 3, v___x_281_);
lean_ctor_set(v___x_285_, 4, v___x_282_);
lean_ctor_set_uint8(v___x_285_, sizeof(void*)*5, v___x_283_);
lean_ctor_set_uint8(v___x_285_, sizeof(void*)*5 + 1, v___x_284_);
v___x_286_ = l_Lake_proc(v___x_285_, v___x_283_, v_a_275_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch___boxed(lean_object* v_repo_287_, lean_object* v_remote_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lake_GitRepo_fetch(v_repo_287_, v_remote_288_, v_a_289_);
return v_res_291_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__2(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_294_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__0));
v___x_295_ = lean_unsigned_to_nat(3u);
v___x_296_ = lean_mk_empty_array_with_capacity(v___x_295_);
v___x_297_ = lean_array_push(v___x_296_, v___x_294_);
return v___x_297_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__3(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__1));
v___x_299_ = lean_obj_once(&l_Lake_GitRepo_checkoutBranch___closed__2, &l_Lake_GitRepo_checkoutBranch___closed__2_once, _init_l_Lake_GitRepo_checkoutBranch___closed__2);
v___x_300_ = lean_array_push(v___x_299_, v___x_298_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object* v_branch_301_, lean_object* v_repo_302_, lean_object* v_a_303_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_305_ = lean_obj_once(&l_Lake_GitRepo_checkoutBranch___closed__3, &l_Lake_GitRepo_checkoutBranch___closed__3_once, _init_l_Lake_GitRepo_checkoutBranch___closed__3);
v___x_306_ = lean_array_push(v___x_305_, v_branch_301_);
v___x_307_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_308_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_309_, 0, v_repo_302_);
v___x_310_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_311_ = 1;
v___x_312_ = 0;
v___x_313_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_313_, 0, v___x_307_);
lean_ctor_set(v___x_313_, 1, v___x_308_);
lean_ctor_set(v___x_313_, 2, v___x_306_);
lean_ctor_set(v___x_313_, 3, v___x_309_);
lean_ctor_set(v___x_313_, 4, v___x_310_);
lean_ctor_set_uint8(v___x_313_, sizeof(void*)*5, v___x_311_);
lean_ctor_set_uint8(v___x_313_, sizeof(void*)*5 + 1, v___x_312_);
v___x_314_ = l_Lake_proc(v___x_313_, v___x_311_, v_a_303_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch___boxed(lean_object* v_branch_315_, lean_object* v_repo_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lake_GitRepo_checkoutBranch(v_branch_315_, v_repo_316_, v_a_317_);
return v_res_319_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__2(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_322_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__0));
v___x_323_ = lean_unsigned_to_nat(4u);
v___x_324_ = lean_mk_empty_array_with_capacity(v___x_323_);
v___x_325_ = lean_array_push(v___x_324_, v___x_322_);
return v___x_325_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__3(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = ((lean_object*)(l_Lake_GitRepo_checkoutDetach___closed__0));
v___x_327_ = lean_obj_once(&l_Lake_GitRepo_checkoutDetach___closed__2, &l_Lake_GitRepo_checkoutDetach___closed__2_once, _init_l_Lake_GitRepo_checkoutDetach___closed__2);
v___x_328_ = lean_array_push(v___x_327_, v___x_326_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object* v_hash_329_, lean_object* v_repo_330_, lean_object* v_a_331_){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; uint8_t v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_333_ = ((lean_object*)(l_Lake_GitRepo_checkoutDetach___closed__1));
v___x_334_ = lean_obj_once(&l_Lake_GitRepo_checkoutDetach___closed__3, &l_Lake_GitRepo_checkoutDetach___closed__3_once, _init_l_Lake_GitRepo_checkoutDetach___closed__3);
v___x_335_ = lean_array_push(v___x_334_, v_hash_329_);
v___x_336_ = lean_array_push(v___x_335_, v___x_333_);
v___x_337_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_338_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v_repo_330_);
v___x_340_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_341_ = 1;
v___x_342_ = 0;
v___x_343_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_343_, 0, v___x_337_);
lean_ctor_set(v___x_343_, 1, v___x_338_);
lean_ctor_set(v___x_343_, 2, v___x_336_);
lean_ctor_set(v___x_343_, 3, v___x_339_);
lean_ctor_set(v___x_343_, 4, v___x_340_);
lean_ctor_set_uint8(v___x_343_, sizeof(void*)*5, v___x_341_);
lean_ctor_set_uint8(v___x_343_, sizeof(void*)*5 + 1, v___x_342_);
v___x_344_ = l_Lake_proc(v___x_343_, v___x_341_, v_a_331_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach___boxed(lean_object* v_hash_345_, lean_object* v_repo_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lake_GitRepo_checkoutDetach(v_hash_345_, v_repo_346_, v_a_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean(lean_object* v_repo_358_, lean_object* v_a_359_){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; uint8_t v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_361_ = ((lean_object*)(l_Lake_GitRepo_clean___closed__2));
v___x_362_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_363_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_364_, 0, v_repo_358_);
v___x_365_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_366_ = 1;
v___x_367_ = 0;
v___x_368_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_368_, 0, v___x_362_);
lean_ctor_set(v___x_368_, 1, v___x_363_);
lean_ctor_set(v___x_368_, 2, v___x_361_);
lean_ctor_set(v___x_368_, 3, v___x_364_);
lean_ctor_set(v___x_368_, 4, v___x_365_);
lean_ctor_set_uint8(v___x_368_, sizeof(void*)*5, v___x_366_);
lean_ctor_set_uint8(v___x_368_, sizeof(void*)*5 + 1, v___x_367_);
v___x_369_ = l_Lake_proc(v___x_368_, v___x_366_, v_a_359_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean___boxed(lean_object* v_repo_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lake_GitRepo_clean(v_repo_370_, v_a_371_);
return v_res_373_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_376_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__0));
v___x_377_ = lean_unsigned_to_nat(4u);
v___x_378_ = lean_mk_empty_array_with_capacity(v___x_377_);
v___x_379_ = lean_array_push(v___x_378_, v___x_376_);
return v___x_379_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_380_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_381_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__2, &l_Lake_GitRepo_resolveRevision_x3f___closed__2_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2);
v___x_382_ = lean_array_push(v___x_381_, v___x_380_);
return v___x_382_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_383_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__1));
v___x_384_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__3, &l_Lake_GitRepo_resolveRevision_x3f___closed__3_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3);
v___x_385_ = lean_array_push(v___x_384_, v___x_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object* v_rev_386_, lean_object* v_repo_387_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_389_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__4, &l_Lake_GitRepo_resolveRevision_x3f___closed__4_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4);
v___x_390_ = lean_array_push(v___x_389_, v_rev_386_);
v___x_391_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_392_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_393_, 0, v_repo_387_);
v___x_394_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_395_ = 1;
v___x_396_ = 0;
v___x_397_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_397_, 0, v___x_391_);
lean_ctor_set(v___x_397_, 1, v___x_392_);
lean_ctor_set(v___x_397_, 2, v___x_390_);
lean_ctor_set(v___x_397_, 3, v___x_393_);
lean_ctor_set(v___x_397_, 4, v___x_394_);
lean_ctor_set_uint8(v___x_397_, sizeof(void*)*5, v___x_395_);
lean_ctor_set_uint8(v___x_397_, sizeof(void*)*5 + 1, v___x_396_);
v___x_398_ = l_Lake_captureProc_x3f(v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f___boxed(lean_object* v_rev_399_, lean_object* v_repo_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_399_, v_repo_400_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision(lean_object* v_rev_405_, lean_object* v_repo_406_, lean_object* v_a_407_){
_start:
{
uint8_t v___x_409_; 
lean_inc_ref(v_rev_405_);
v___x_409_ = l_Lake_Git_isFullObjectName(v_rev_405_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; 
lean_inc_ref(v_repo_406_);
lean_inc_ref(v_rev_405_);
v___x_410_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_405_, v_repo_406_);
if (lean_obj_tag(v___x_410_) == 1)
{
lean_object* v_val_411_; lean_object* v___x_412_; 
lean_dec_ref(v_repo_406_);
lean_dec_ref(v_rev_405_);
v_val_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_val_411_);
lean_dec_ref(v___x_410_);
v___x_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_412_, 0, v_val_411_);
lean_ctor_set(v___x_412_, 1, v_a_407_);
return v___x_412_;
}
else
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; uint8_t v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec(v___x_410_);
v___x_413_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__0));
v___x_414_ = lean_string_append(v_repo_406_, v___x_413_);
v___x_415_ = lean_string_append(v___x_414_, v_rev_405_);
lean_dec_ref(v_rev_405_);
v___x_416_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__1));
v___x_417_ = lean_string_append(v___x_415_, v___x_416_);
v___x_418_ = 3;
v___x_419_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_419_, 0, v___x_417_);
lean_ctor_set_uint8(v___x_419_, sizeof(void*)*1, v___x_418_);
v___x_420_ = lean_array_get_size(v_a_407_);
v___x_421_ = lean_array_push(v_a_407_, v___x_419_);
v___x_422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_420_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
return v___x_422_;
}
}
else
{
lean_object* v___x_423_; 
lean_dec_ref(v_repo_406_);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v_rev_405_);
lean_ctor_set(v___x_423_, 1, v_a_407_);
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision___boxed(lean_object* v_rev_424_, lean_object* v_repo_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lake_GitRepo_resolveRevision(v_rev_424_, v_repo_425_, v_a_426_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object* v_repo_430_){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevision_x3f___closed__0));
v___x_433_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_432_, v_repo_430_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f___boxed(lean_object* v_repo_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lake_GitRepo_getHeadRevision_x3f(v_repo_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object* v_repo_438_, lean_object* v_a_439_){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevision_x3f___closed__0));
lean_inc_ref(v_repo_438_);
v___x_442_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_441_, v_repo_438_);
if (lean_obj_tag(v___x_442_) == 1)
{
lean_object* v_val_443_; lean_object* v___x_444_; 
lean_dec_ref(v_repo_438_);
v_val_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_val_443_);
lean_dec_ref(v___x_442_);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v_val_443_);
lean_ctor_set(v___x_444_, 1, v_a_439_);
return v___x_444_;
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
lean_dec(v___x_442_);
v___x_445_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevision___closed__0));
v___x_446_ = lean_string_append(v_repo_438_, v___x_445_);
v___x_447_ = 3;
v___x_448_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set_uint8(v___x_448_, sizeof(void*)*1, v___x_447_);
v___x_449_ = lean_array_get_size(v_a_439_);
v___x_450_ = lean_array_push(v_a_439_, v___x_448_);
v___x_451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision___boxed(lean_object* v_repo_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lake_GitRepo_getHeadRevision(v_repo_452_, v_a_453_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(lean_object* v_s_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0));
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___boxed(lean_object* v_s_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v_s_460_);
lean_dec_ref(v_s_460_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(lean_object* v___x_462_, lean_object* v___x_463_, lean_object* v___x_464_, lean_object* v_a_465_, lean_object* v_b_466_){
_start:
{
lean_object* v_it_468_; lean_object* v_startInclusive_469_; lean_object* v_endExclusive_470_; 
if (lean_obj_tag(v_a_465_) == 0)
{
lean_object* v_currPos_475_; lean_object* v_searcher_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_502_; 
v_currPos_475_ = lean_ctor_get(v_a_465_, 0);
v_searcher_476_ = lean_ctor_get(v_a_465_, 1);
v_isSharedCheck_502_ = !lean_is_exclusive(v_a_465_);
if (v_isSharedCheck_502_ == 0)
{
v___x_478_ = v_a_465_;
v_isShared_479_ = v_isSharedCheck_502_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_searcher_476_);
lean_inc(v_currPos_475_);
lean_dec(v_a_465_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_502_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v_startInclusive_480_; lean_object* v_endExclusive_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_startInclusive_480_ = lean_ctor_get(v___x_463_, 1);
v_endExclusive_481_ = lean_ctor_get(v___x_463_, 2);
v___x_482_ = lean_nat_sub(v_endExclusive_481_, v_startInclusive_480_);
v___x_483_ = lean_nat_dec_eq(v_searcher_476_, v___x_482_);
lean_dec(v___x_482_);
if (v___x_483_ == 0)
{
uint32_t v___x_484_; uint32_t v___x_485_; uint8_t v___x_486_; 
v___x_484_ = 10;
v___x_485_ = lean_string_utf8_get_fast(v___x_462_, v_searcher_476_);
v___x_486_ = lean_uint32_dec_eq(v___x_485_, v___x_484_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_487_ = lean_string_utf8_next_fast(v___x_462_, v_searcher_476_);
lean_dec(v_searcher_476_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v___x_487_);
v___x_489_ = v___x_478_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_currPos_475_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v___x_487_);
v___x_489_ = v_reuseFailAlloc_491_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
v_a_465_ = v___x_489_;
goto _start;
}
}
else
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v_slice_495_; lean_object* v_nextIt_497_; 
v___x_492_ = lean_string_utf8_next_fast(v___x_462_, v_searcher_476_);
v___x_493_ = lean_nat_sub(v___x_492_, v_searcher_476_);
v___x_494_ = lean_nat_add(v_searcher_476_, v___x_493_);
lean_dec(v___x_493_);
v_slice_495_ = l_String_Slice_subslice_x21(v___x_463_, v_currPos_475_, v_searcher_476_);
lean_inc(v___x_494_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v___x_494_);
lean_ctor_set(v___x_478_, 0, v___x_494_);
v_nextIt_497_ = v___x_478_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_494_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v___x_494_);
v_nextIt_497_ = v_reuseFailAlloc_500_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v_startInclusive_498_; lean_object* v_endExclusive_499_; 
v_startInclusive_498_ = lean_ctor_get(v_slice_495_, 0);
lean_inc(v_startInclusive_498_);
v_endExclusive_499_ = lean_ctor_get(v_slice_495_, 1);
lean_inc(v_endExclusive_499_);
lean_dec_ref(v_slice_495_);
v_it_468_ = v_nextIt_497_;
v_startInclusive_469_ = v_startInclusive_498_;
v_endExclusive_470_ = v_endExclusive_499_;
goto v___jp_467_;
}
}
}
else
{
lean_object* v___x_501_; 
lean_del_object(v___x_478_);
lean_dec(v_searcher_476_);
v___x_501_ = lean_box(1);
lean_inc(v___x_464_);
v_it_468_ = v___x_501_;
v_startInclusive_469_ = v_currPos_475_;
v_endExclusive_470_ = v___x_464_;
goto v___jp_467_;
}
}
}
else
{
lean_dec(v___x_464_);
lean_dec_ref(v___x_462_);
return v_b_466_;
}
v___jp_467_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
lean_inc_ref(v___x_462_);
v___x_471_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_471_, 0, v___x_462_);
lean_ctor_set(v___x_471_, 1, v_startInclusive_469_);
lean_ctor_set(v___x_471_, 2, v_endExclusive_470_);
v___x_472_ = l_String_Slice_toString(v___x_471_);
lean_dec_ref(v___x_471_);
v___x_473_ = lean_array_push(v_b_466_, v___x_472_);
v_a_465_ = v_it_468_;
v_b_466_ = v___x_473_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___boxed(lean_object* v___x_503_, lean_object* v___x_504_, lean_object* v___x_505_, lean_object* v_a_506_, lean_object* v_b_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_503_, v___x_504_, v___x_505_, v_a_506_, v_b_507_);
lean_dec_ref(v___x_504_);
return v_res_508_;
}
}
static lean_object* _init_l_Lake_GitRepo_getHeadRevisions___closed__3(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_517_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevisions___closed__2));
v___x_518_ = lean_unsigned_to_nat(2u);
v___x_519_ = lean_mk_empty_array_with_capacity(v___x_518_);
v___x_520_ = lean_array_push(v___x_519_, v___x_517_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions(lean_object* v_repo_521_, lean_object* v_n_522_, lean_object* v_a_523_){
_start:
{
lean_object* v___y_526_; lean_object* v_args_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v_args_572_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevisions___closed__1));
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = lean_nat_dec_eq(v_n_522_, v___x_573_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_575_ = l_Nat_reprFast(v_n_522_);
v___x_576_ = lean_obj_once(&l_Lake_GitRepo_getHeadRevisions___closed__3, &l_Lake_GitRepo_getHeadRevisions___closed__3_once, _init_l_Lake_GitRepo_getHeadRevisions___closed__3);
v___x_577_ = lean_array_push(v___x_576_, v___x_575_);
v___x_578_ = l_Array_append___redArg(v_args_572_, v___x_577_);
lean_dec_ref(v___x_577_);
v___y_526_ = v___x_578_;
goto v___jp_525_;
}
else
{
lean_dec(v_n_522_);
v___y_526_ = v_args_572_;
goto v___jp_525_;
}
v___jp_525_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; uint8_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_527_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_528_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v_repo_521_);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_532_ = 1;
v___x_533_ = 0;
v___x_534_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_534_, 0, v___x_527_);
lean_ctor_set(v___x_534_, 1, v___x_528_);
lean_ctor_set(v___x_534_, 2, v___y_526_);
lean_ctor_set(v___x_534_, 3, v___x_529_);
lean_ctor_set(v___x_534_, 4, v___x_531_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*5, v___x_532_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*5 + 1, v___x_533_);
v___x_535_ = l_Lake_captureProc_x27(v___x_534_, v_a_523_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_562_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
v_a_537_ = lean_ctor_get(v___x_535_, 1);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_562_ == 0)
{
v___x_539_ = v___x_535_;
v_isShared_540_ = v_isSharedCheck_562_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_inc(v_a_536_);
lean_dec(v___x_535_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_562_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v_stdout_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v_str_545_; lean_object* v_startInclusive_546_; lean_object* v_endExclusive_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_561_; 
v_stdout_541_ = lean_ctor_get(v_a_536_, 0);
lean_inc_ref(v_stdout_541_);
lean_dec(v_a_536_);
v___x_542_ = lean_string_utf8_byte_size(v_stdout_541_);
v___x_543_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_543_, 0, v_stdout_541_);
lean_ctor_set(v___x_543_, 1, v___x_530_);
lean_ctor_set(v___x_543_, 2, v___x_542_);
v___x_544_ = l_String_Slice_trimAscii(v___x_543_);
v_str_545_ = lean_ctor_get(v___x_544_, 0);
v_startInclusive_546_ = lean_ctor_get(v___x_544_, 1);
v_endExclusive_547_ = lean_ctor_get(v___x_544_, 2);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_561_ == 0)
{
v___x_549_ = v___x_544_;
v_isShared_550_ = v_isSharedCheck_561_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_endExclusive_547_);
lean_inc(v_startInclusive_546_);
lean_inc(v_str_545_);
lean_dec(v___x_544_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_561_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_551_ = lean_string_utf8_extract(v_str_545_, v_startInclusive_546_, v_endExclusive_547_);
lean_dec(v_endExclusive_547_);
lean_dec(v_startInclusive_546_);
lean_dec_ref(v_str_545_);
v___x_552_ = lean_string_utf8_byte_size(v___x_551_);
lean_inc_ref(v___x_551_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 2, v___x_552_);
lean_ctor_set(v___x_549_, 1, v___x_530_);
lean_ctor_set(v___x_549_, 0, v___x_551_);
v___x_554_ = v___x_549_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v___x_552_);
v___x_554_ = v_reuseFailAlloc_560_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_555_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v___x_554_);
v___x_556_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_551_, v___x_554_, v___x_552_, v___x_555_, v___x_531_);
lean_dec_ref(v___x_554_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v___x_556_);
v___x_558_ = v___x_539_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_a_537_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
else
{
lean_object* v_a_563_; lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
v_a_563_ = lean_ctor_get(v___x_535_, 0);
v_a_564_ = lean_ctor_get(v___x_535_, 1);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_535_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_inc(v_a_563_);
lean_dec(v___x_535_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_563_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions___boxed(lean_object* v_repo_579_, lean_object* v_n_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lake_GitRepo_getHeadRevisions(v_repo_579_, v_n_580_, v_a_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(lean_object* v___x_584_, lean_object* v___x_585_, lean_object* v___x_586_, lean_object* v_inst_587_, lean_object* v_R_588_, lean_object* v_a_589_, lean_object* v_b_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_584_, v___x_585_, v___x_586_, v_a_589_, v_b_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___boxed(lean_object* v___x_592_, lean_object* v___x_593_, lean_object* v___x_594_, lean_object* v_inst_595_, lean_object* v_R_596_, lean_object* v_a_597_, lean_object* v_b_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(v___x_592_, v___x_593_, v___x_594_, v_inst_595_, v_R_596_, v_a_597_, v_b_598_);
lean_dec_ref(v___x_593_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object* v_rev_601_, lean_object* v_remote_602_, lean_object* v_repo_603_, lean_object* v_a_604_){
_start:
{
uint8_t v___x_606_; 
lean_inc_ref(v_rev_601_);
v___x_606_ = l_Lake_Git_isFullObjectName(v_rev_601_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_607_ = ((lean_object*)(l_Lake_GitRepo_resolveRemoteRevision___closed__0));
v___x_608_ = lean_string_append(v_remote_602_, v___x_607_);
v___x_609_ = lean_string_append(v___x_608_, v_rev_601_);
lean_inc_ref(v_repo_603_);
v___x_610_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_609_, v_repo_603_);
if (lean_obj_tag(v___x_610_) == 1)
{
lean_object* v_val_611_; lean_object* v___x_612_; 
lean_dec_ref(v_repo_603_);
lean_dec_ref(v_rev_601_);
v_val_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_val_611_);
lean_dec_ref(v___x_610_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v_val_611_);
lean_ctor_set(v___x_612_, 1, v_a_604_);
return v___x_612_;
}
else
{
lean_object* v___x_613_; 
lean_dec(v___x_610_);
lean_inc_ref(v_repo_603_);
lean_inc_ref(v_rev_601_);
v___x_613_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_601_, v_repo_603_);
if (lean_obj_tag(v___x_613_) == 1)
{
lean_object* v_val_614_; lean_object* v___x_615_; 
lean_dec_ref(v_repo_603_);
lean_dec_ref(v_rev_601_);
v_val_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_val_614_);
lean_dec_ref(v___x_613_);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v_val_614_);
lean_ctor_set(v___x_615_, 1, v_a_604_);
return v___x_615_;
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec(v___x_613_);
v___x_616_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__0));
v___x_617_ = lean_string_append(v_repo_603_, v___x_616_);
v___x_618_ = lean_string_append(v___x_617_, v_rev_601_);
lean_dec_ref(v_rev_601_);
v___x_619_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__1));
v___x_620_ = lean_string_append(v___x_618_, v___x_619_);
v___x_621_ = 3;
v___x_622_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set_uint8(v___x_622_, sizeof(void*)*1, v___x_621_);
v___x_623_ = lean_array_get_size(v_a_604_);
v___x_624_ = lean_array_push(v_a_604_, v___x_622_);
v___x_625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
return v___x_625_;
}
}
}
else
{
lean_object* v___x_626_; 
lean_dec_ref(v_repo_603_);
lean_dec_ref(v_remote_602_);
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v_rev_601_);
lean_ctor_set(v___x_626_, 1, v_a_604_);
return v___x_626_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___boxed(lean_object* v_rev_627_, lean_object* v_remote_628_, lean_object* v_repo_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lake_GitRepo_resolveRemoteRevision(v_rev_627_, v_remote_628_, v_repo_629_, v_a_630_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object* v_repo_633_, lean_object* v_rev_x3f_634_, lean_object* v_remote_635_, lean_object* v_a_636_){
_start:
{
lean_object* v___x_638_; 
lean_inc_ref(v_remote_635_);
lean_inc_ref(v_repo_633_);
v___x_638_ = l_Lake_GitRepo_fetch(v_repo_633_, v_remote_635_, v_a_636_);
if (lean_obj_tag(v___x_638_) == 0)
{
if (lean_obj_tag(v_rev_x3f_634_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v_a_639_ = lean_ctor_get(v___x_638_, 1);
lean_inc(v_a_639_);
lean_dec_ref(v___x_638_);
v___x_640_ = ((lean_object*)(l_Lake_Git_upstreamBranch___closed__0));
v___x_641_ = l_Lake_GitRepo_resolveRemoteRevision(v___x_640_, v_remote_635_, v_repo_633_, v_a_639_);
return v___x_641_;
}
else
{
lean_object* v_a_642_; lean_object* v_val_643_; lean_object* v___x_644_; 
v_a_642_ = lean_ctor_get(v___x_638_, 1);
lean_inc(v_a_642_);
lean_dec_ref(v___x_638_);
v_val_643_ = lean_ctor_get(v_rev_x3f_634_, 0);
lean_inc(v_val_643_);
lean_dec_ref(v_rev_x3f_634_);
v___x_644_ = l_Lake_GitRepo_resolveRemoteRevision(v_val_643_, v_remote_635_, v_repo_633_, v_a_642_);
return v___x_644_;
}
}
else
{
lean_object* v_a_645_; lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec_ref(v_remote_635_);
lean_dec(v_rev_x3f_634_);
lean_dec_ref(v_repo_633_);
v_a_645_ = lean_ctor_get(v___x_638_, 0);
v_a_646_ = lean_ctor_get(v___x_638_, 1);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_638_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_inc(v_a_645_);
lean_dec(v___x_638_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_645_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision___boxed(lean_object* v_repo_654_, lean_object* v_rev_x3f_655_, lean_object* v_remote_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lake_GitRepo_findRemoteRevision(v_repo_654_, v_rev_x3f_655_, v_remote_656_, v_a_657_);
return v_res_659_;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__2(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_662_ = ((lean_object*)(l_Lake_GitRepo_branchExists___closed__0));
v___x_663_ = lean_unsigned_to_nat(3u);
v___x_664_ = lean_mk_empty_array_with_capacity(v___x_663_);
v___x_665_ = lean_array_push(v___x_664_, v___x_662_);
return v___x_665_;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__3(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_667_ = lean_obj_once(&l_Lake_GitRepo_branchExists___closed__2, &l_Lake_GitRepo_branchExists___closed__2_once, _init_l_Lake_GitRepo_branchExists___closed__2);
v___x_668_ = lean_array_push(v___x_667_, v___x_666_);
return v___x_668_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_branchExists(lean_object* v_rev_669_, lean_object* v_repo_670_){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; uint8_t v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_672_ = ((lean_object*)(l_Lake_GitRepo_branchExists___closed__1));
v___x_673_ = lean_string_append(v___x_672_, v_rev_669_);
v___x_674_ = lean_obj_once(&l_Lake_GitRepo_branchExists___closed__3, &l_Lake_GitRepo_branchExists___closed__3_once, _init_l_Lake_GitRepo_branchExists___closed__3);
v___x_675_ = lean_array_push(v___x_674_, v___x_673_);
v___x_676_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_677_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_678_, 0, v_repo_670_);
v___x_679_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_680_ = 1;
v___x_681_ = 0;
v___x_682_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_682_, 0, v___x_676_);
lean_ctor_set(v___x_682_, 1, v___x_677_);
lean_ctor_set(v___x_682_, 2, v___x_675_);
lean_ctor_set(v___x_682_, 3, v___x_678_);
lean_ctor_set(v___x_682_, 4, v___x_679_);
lean_ctor_set_uint8(v___x_682_, sizeof(void*)*5, v___x_680_);
lean_ctor_set_uint8(v___x_682_, sizeof(void*)*5 + 1, v___x_681_);
v___x_683_ = l_Lake_testProc(v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object* v_rev_684_, lean_object* v_repo_685_, lean_object* v_a_686_){
_start:
{
uint8_t v_res_687_; lean_object* v_r_688_; 
v_res_687_ = l_Lake_GitRepo_branchExists(v_rev_684_, v_repo_685_);
lean_dec_ref(v_rev_684_);
v_r_688_ = lean_box(v_res_687_);
return v_r_688_;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__1(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_690_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__0));
v___x_691_ = lean_unsigned_to_nat(3u);
v___x_692_ = lean_mk_empty_array_with_capacity(v___x_691_);
v___x_693_ = lean_array_push(v___x_692_, v___x_690_);
return v___x_693_;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__2(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_695_ = lean_obj_once(&l_Lake_GitRepo_revisionExists___closed__1, &l_Lake_GitRepo_revisionExists___closed__1_once, _init_l_Lake_GitRepo_revisionExists___closed__1);
v___x_696_ = lean_array_push(v___x_695_, v___x_694_);
return v___x_696_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_revisionExists(lean_object* v_rev_697_, lean_object* v_repo_698_){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; uint8_t v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_700_ = ((lean_object*)(l_Lake_GitRepo_revisionExists___closed__0));
v___x_701_ = lean_string_append(v_rev_697_, v___x_700_);
v___x_702_ = lean_obj_once(&l_Lake_GitRepo_revisionExists___closed__2, &l_Lake_GitRepo_revisionExists___closed__2_once, _init_l_Lake_GitRepo_revisionExists___closed__2);
v___x_703_ = lean_array_push(v___x_702_, v___x_701_);
v___x_704_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_705_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_706_, 0, v_repo_698_);
v___x_707_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_708_ = 1;
v___x_709_ = 0;
v___x_710_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_710_, 0, v___x_704_);
lean_ctor_set(v___x_710_, 1, v___x_705_);
lean_ctor_set(v___x_710_, 2, v___x_703_);
lean_ctor_set(v___x_710_, 3, v___x_706_);
lean_ctor_set(v___x_710_, 4, v___x_707_);
lean_ctor_set_uint8(v___x_710_, sizeof(void*)*5, v___x_708_);
lean_ctor_set_uint8(v___x_710_, sizeof(void*)*5 + 1, v___x_709_);
v___x_711_ = l_Lake_testProc(v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists___boxed(lean_object* v_rev_712_, lean_object* v_repo_713_, lean_object* v_a_714_){
_start:
{
uint8_t v_res_715_; lean_object* v_r_716_; 
v_res_715_ = l_Lake_GitRepo_revisionExists(v_rev_712_, v_repo_713_);
v_r_716_ = lean_box(v_res_715_);
return v_r_716_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags(lean_object* v_repo_722_){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; uint8_t v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_724_ = ((lean_object*)(l_Lake_GitRepo_getTags___closed__1));
v___x_725_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_726_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_727_, 0, v_repo_722_);
v___x_728_ = lean_unsigned_to_nat(0u);
v___x_729_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_730_ = 1;
v___x_731_ = 0;
v___x_732_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_732_, 0, v___x_725_);
lean_ctor_set(v___x_732_, 1, v___x_726_);
lean_ctor_set(v___x_732_, 2, v___x_724_);
lean_ctor_set(v___x_732_, 3, v___x_727_);
lean_ctor_set(v___x_732_, 4, v___x_729_);
lean_ctor_set_uint8(v___x_732_, sizeof(void*)*5, v___x_730_);
lean_ctor_set_uint8(v___x_732_, sizeof(void*)*5 + 1, v___x_731_);
v___x_733_ = l_Lake_captureProc_x3f(v___x_732_);
if (lean_obj_tag(v___x_733_) == 1)
{
lean_object* v_val_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_val_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc_n(v_val_734_, 2);
lean_dec_ref(v___x_733_);
v___x_735_ = lean_string_utf8_byte_size(v_val_734_);
v___x_736_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_736_, 0, v_val_734_);
lean_ctor_set(v___x_736_, 1, v___x_728_);
lean_ctor_set(v___x_736_, 2, v___x_735_);
v___x_737_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v___x_736_);
v___x_738_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v_val_734_, v___x_736_, v___x_735_, v___x_737_, v___x_729_);
lean_dec_ref(v___x_736_);
v___x_739_ = lean_array_to_list(v___x_738_);
return v___x_739_;
}
else
{
lean_object* v___x_740_; 
lean_dec(v___x_733_);
v___x_740_ = lean_box(0);
return v___x_740_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags___boxed(lean_object* v_repo_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lake_GitRepo_getTags(v_repo_741_);
return v_res_743_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__2(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_746_ = ((lean_object*)(l_Lake_GitRepo_findTag_x3f___closed__0));
v___x_747_ = lean_unsigned_to_nat(4u);
v___x_748_ = lean_mk_empty_array_with_capacity(v___x_747_);
v___x_749_ = lean_array_push(v___x_748_, v___x_746_);
return v___x_749_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__3(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_750_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_751_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__2, &l_Lake_GitRepo_findTag_x3f___closed__2_once, _init_l_Lake_GitRepo_findTag_x3f___closed__2);
v___x_752_ = lean_array_push(v___x_751_, v___x_750_);
return v___x_752_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__4(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = ((lean_object*)(l_Lake_GitRepo_findTag_x3f___closed__1));
v___x_754_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__3, &l_Lake_GitRepo_findTag_x3f___closed__3_once, _init_l_Lake_GitRepo_findTag_x3f___closed__3);
v___x_755_ = lean_array_push(v___x_754_, v___x_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object* v_rev_756_, lean_object* v_repo_757_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; uint8_t v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_759_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__4, &l_Lake_GitRepo_findTag_x3f___closed__4_once, _init_l_Lake_GitRepo_findTag_x3f___closed__4);
v___x_760_ = lean_array_push(v___x_759_, v_rev_756_);
v___x_761_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_762_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_763_, 0, v_repo_757_);
v___x_764_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_765_ = 1;
v___x_766_ = 0;
v___x_767_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_767_, 0, v___x_761_);
lean_ctor_set(v___x_767_, 1, v___x_762_);
lean_ctor_set(v___x_767_, 2, v___x_760_);
lean_ctor_set(v___x_767_, 3, v___x_763_);
lean_ctor_set(v___x_767_, 4, v___x_764_);
lean_ctor_set_uint8(v___x_767_, sizeof(void*)*5, v___x_765_);
lean_ctor_set_uint8(v___x_767_, sizeof(void*)*5 + 1, v___x_766_);
v___x_768_ = l_Lake_captureProc_x3f(v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f___boxed(lean_object* v_rev_769_, lean_object* v_repo_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lake_GitRepo_findTag_x3f(v_rev_769_, v_repo_770_);
return v_res_772_;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_775_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__0));
v___x_776_ = lean_unsigned_to_nat(3u);
v___x_777_ = lean_mk_empty_array_with_capacity(v___x_776_);
v___x_778_ = lean_array_push(v___x_777_, v___x_775_);
return v___x_778_;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3(void){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_779_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__1));
v___x_780_ = lean_obj_once(&l_Lake_GitRepo_getRemoteUrl_x3f___closed__2, &l_Lake_GitRepo_getRemoteUrl_x3f___closed__2_once, _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2);
v___x_781_ = lean_array_push(v___x_780_, v___x_779_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object* v_remote_782_, lean_object* v_repo_783_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; uint8_t v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_785_ = lean_obj_once(&l_Lake_GitRepo_getRemoteUrl_x3f___closed__3, &l_Lake_GitRepo_getRemoteUrl_x3f___closed__3_once, _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3);
v___x_786_ = lean_array_push(v___x_785_, v_remote_782_);
v___x_787_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_788_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_789_, 0, v_repo_783_);
v___x_790_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_791_ = 1;
v___x_792_ = 0;
v___x_793_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_793_, 0, v___x_787_);
lean_ctor_set(v___x_793_, 1, v___x_788_);
lean_ctor_set(v___x_793_, 2, v___x_786_);
lean_ctor_set(v___x_793_, 3, v___x_789_);
lean_ctor_set(v___x_793_, 4, v___x_790_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*5, v___x_791_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*5 + 1, v___x_792_);
v___x_794_ = l_Lake_captureProc_x3f(v___x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___boxed(lean_object* v_remote_795_, lean_object* v_repo_796_, lean_object* v_a_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lake_GitRepo_getRemoteUrl_x3f(v_remote_795_, v_repo_796_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object* v_remote_799_, lean_object* v_repo_800_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lake_GitRepo_getRemoteUrl_x3f(v_remote_799_, v_repo_800_);
if (lean_obj_tag(v___x_802_) == 0)
{
return v___x_802_;
}
else
{
lean_object* v_val_803_; lean_object* v___x_804_; 
v_val_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_val_803_);
lean_dec_ref(v___x_802_);
v___x_804_ = l_Lake_Git_filterUrl_x3f(v_val_803_);
return v___x_804_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f___boxed(lean_object* v_remote_805_, lean_object* v_repo_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v_remote_805_, v_repo_806_);
return v_res_808_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasNoDiff(lean_object* v_repo_819_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; uint8_t v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_821_ = ((lean_object*)(l_Lake_GitRepo_hasNoDiff___closed__2));
v___x_822_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_823_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_824_, 0, v_repo_819_);
v___x_825_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_826_ = 1;
v___x_827_ = 0;
v___x_828_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_828_, 0, v___x_822_);
lean_ctor_set(v___x_828_, 1, v___x_823_);
lean_ctor_set(v___x_828_, 2, v___x_821_);
lean_ctor_set(v___x_828_, 3, v___x_824_);
lean_ctor_set(v___x_828_, 4, v___x_825_);
lean_ctor_set_uint8(v___x_828_, sizeof(void*)*5, v___x_826_);
lean_ctor_set_uint8(v___x_828_, sizeof(void*)*5 + 1, v___x_827_);
v___x_829_ = l_Lake_testProc(v___x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff___boxed(lean_object* v_repo_830_, lean_object* v_a_831_){
_start:
{
uint8_t v_res_832_; lean_object* v_r_833_; 
v_res_832_ = l_Lake_GitRepo_hasNoDiff(v_repo_830_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasDiff(lean_object* v_repo_834_){
_start:
{
uint8_t v___x_836_; 
v___x_836_ = l_Lake_GitRepo_hasNoDiff(v_repo_834_);
if (v___x_836_ == 0)
{
uint8_t v___x_837_; 
v___x_837_ = 1;
return v___x_837_;
}
else
{
uint8_t v___x_838_; 
v___x_838_ = 0;
return v___x_838_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff___boxed(lean_object* v_repo_839_, lean_object* v_a_840_){
_start:
{
uint8_t v_res_841_; lean_object* v_r_842_; 
v_res_841_ = l_Lake_GitRepo_hasDiff(v_repo_839_);
v_r_842_ = lean_box(v_res_841_);
return v_r_842_;
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
