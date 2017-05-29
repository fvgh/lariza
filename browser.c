#include <fcntl.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>

#include <gdk/gdkkeysyms.h>
#include <gio/gio.h>
#include <gtk/gtk.h>
#include <gtk/gtkx.h>
#include <webkit2/webkit2.h>


struct Client
{
    gchar *context_menu_uri;
    gchar *hover_uri;
    GtkWidget *location;
    GtkWidget *vbox;
    GtkWidget *web_view;
    GtkWidget *win;
};

struct CommandArguments
{
    gchar *string;
};

struct DownloadManager
{
    GtkWidget *scroll;
    GtkWidget *toolbar;
    GtkWidget *win;
} dm;


static void client_destroy(GtkWidget *, gpointer);
static gboolean client_destroy_request(WebKitWebView *, gpointer);
static WebKitWebView *client_new(const gchar *, WebKitWebView *, gboolean);
static WebKitWebView *client_new_request(WebKitWebView *, WebKitNavigationAction *,
                                         gpointer);
static gboolean command_abort_load(struct Client *, struct CommandArguments *);
static gboolean command_close(struct Client *, struct CommandArguments *);
static gboolean command_download_manager_close(struct Client *, struct CommandArguments *);
static gboolean command_download_manager_open(struct Client *, struct CommandArguments *);
static gboolean command_focus_input_box(struct Client *, struct CommandArguments *);
static gboolean command_go_backward(struct Client *, struct CommandArguments *);
static gboolean command_go_forward(struct Client *, struct CommandArguments *);
static gboolean command_go_uri_new_window(struct Client *, struct CommandArguments *);
static gboolean command_go_uri(struct Client *, struct CommandArguments *);
static gboolean command_reload(struct Client *, struct CommandArguments *);
static gboolean command_reload_user_certs(struct Client *, struct CommandArguments *);
static gboolean command_search_backward(struct Client *, struct CommandArguments *);
static gboolean command_search_forward(struct Client *, struct CommandArguments *);
static gboolean command_search_new(struct Client *, struct CommandArguments *);
static gboolean command_zoom_decrease(struct Client *, struct CommandArguments *);
static gboolean command_zoom_increase(struct Client *, struct CommandArguments *);
static gboolean command_zoom_reset(struct Client *, struct CommandArguments *);
static void cooperation_setup(void);
static void changed_download_progress(GObject *, GParamSpec *, gpointer);
static void changed_load_progress(GObject *, GParamSpec *, gpointer);
static void changed_title(GObject *, GParamSpec *, gpointer);
static void changed_uri(GObject *, GParamSpec *, gpointer);
static gboolean crashed_web_view(WebKitWebView *, gpointer);
static gboolean decide_policy(WebKitWebView *, WebKitPolicyDecision *,
                              WebKitPolicyDecisionType, gpointer);
static gboolean download_handle(WebKitDownload *, gchar *, gpointer);
static void download_handle_start(WebKitWebView *, WebKitDownload *, gpointer);
static void downloadmanager_cancel(GtkToolButton *, gpointer data);
static gboolean downloadmanager_delete(GtkWidget *, gpointer);
static void downloadmanager_setup(void);
static gchar *ensure_uri_scheme(const gchar *);
static void grab_environment_configuration(void);
static void hover_web_view(WebKitWebView *, WebKitHitTestResult *, guint, gpointer);
static gchar *human_event(GdkEvent *);
static gboolean input_driver(struct Client *, gchar *, gchar *, const gchar *);
static gboolean input_driver_context_menu(GtkAction *, gpointer);
static gboolean input_driver_execute_command(gchar *, struct Client *);
static gboolean input_driver_run_if_needed(void);
static gboolean key_common(GtkWidget *, GdkEvent *, gpointer);
static gboolean key_location(GtkWidget *, GdkEvent *, gpointer);
static void load_command_hash(void);
static gboolean menu_web_view(WebKitWebView *, WebKitContextMenu *, GdkEvent *,
                              WebKitHitTestResult *, gpointer);
static gboolean quit_if_nothing_active(void);
static gboolean remote_msg(GIOChannel *, GIOCondition, gpointer);
static void search(struct Client *, gint);
static void show_web_view(WebKitWebView *, gpointer);
static Window tabbed_launch(void);
static void trust_user_certs(WebKitWebContext *);


static const gchar *accepted_language[2] = { NULL, NULL };
static gint clients = 0, downloads = 0;
static GHashTable *command_hash = NULL;
static gboolean cooperative_alone = TRUE;
static gboolean cooperative_instances = TRUE;
static int cooperative_pipe_fp = 0;
static gchar *download_dir = "/var/tmp";
static gboolean enable_webgl = FALSE;
static Window embed = 0;
static gchar *fifo_suffix = "main";
static gdouble global_zoom = 1.0;
static gchar *history_file = NULL;
static GPid indriv_pid = -1;
static gint indriv_stdin = -1;
static GIOChannel *indriv_stdout_channel = NULL;
static gboolean initial_wc_setup_done = FALSE;
static gchar *search_prefix = ":/";
static gchar *search_text = NULL;
static gboolean tabbed_automagic = TRUE;
static gchar *user_agent = NULL;


void
client_destroy(GtkWidget *widget, gpointer data)
{
    struct Client *c = (struct Client *)data;

    g_signal_handlers_disconnect_by_func(G_OBJECT(c->web_view),
                                         changed_load_progress, c);

    free(c);
    clients--;

    quit_if_nothing_active();
}

gboolean
client_destroy_request(WebKitWebView *web_view, gpointer data)
{
    struct Client *c = (struct Client *)data;

    gtk_widget_destroy(c->win);

    return TRUE;
}

WebKitWebView *
client_new(const gchar *uri, WebKitWebView *related_wv, gboolean show)
{
    struct Client *c;
    WebKitWebContext *wc;
    gchar *f;

    if (uri != NULL && cooperative_instances && !cooperative_alone)
    {
        write(cooperative_pipe_fp, "go_uri_new_window ", strlen("go_uri_new_window "));
        write(cooperative_pipe_fp, uri, strlen(uri));
        write(cooperative_pipe_fp, "\n", 1);
        return NULL;
    }

    c = calloc(1, sizeof(struct Client));
    if (!c)
    {
        fprintf(stderr, __NAME__": Fatal: calloc failed\n");
        exit(EXIT_FAILURE);
    }

    if (embed != 0)
    {
        c->win = gtk_plug_new(embed);
        if (!gtk_plug_get_embedded(GTK_PLUG(c->win)))
        {
            fprintf(stderr, __NAME__": Can't plug-in to XID %ld.\n", embed);
            gtk_widget_destroy(c->win);
            c->win = NULL;
            embed = 0;
        }
    }

    if (c->win == NULL)
        c->win = gtk_window_new(GTK_WINDOW_TOPLEVEL);

    gtk_window_set_default_size(GTK_WINDOW(c->win), 800, 600);

    g_signal_connect(G_OBJECT(c->win), "destroy", G_CALLBACK(client_destroy), c);
    gtk_window_set_title(GTK_WINDOW(c->win), __NAME__);

    if (related_wv == NULL)
        c->web_view = webkit_web_view_new();
    else
        c->web_view = webkit_web_view_new_with_related_view(related_wv);
    wc = webkit_web_view_get_context(WEBKIT_WEB_VIEW(c->web_view));

    webkit_web_view_set_zoom_level(WEBKIT_WEB_VIEW(c->web_view), global_zoom);
    g_signal_connect(G_OBJECT(c->web_view), "notify::title",
                     G_CALLBACK(changed_title), c);
    g_signal_connect(G_OBJECT(c->web_view), "notify::uri",
                     G_CALLBACK(changed_uri), c);
    g_signal_connect(G_OBJECT(c->web_view), "notify::estimated-load-progress",
                     G_CALLBACK(changed_load_progress), c);
    g_signal_connect(G_OBJECT(c->web_view), "create",
                     G_CALLBACK(client_new_request), NULL);
    g_signal_connect(G_OBJECT(c->web_view), "context-menu",
                     G_CALLBACK(menu_web_view), c);
    g_signal_connect(G_OBJECT(c->web_view), "close",
                     G_CALLBACK(client_destroy_request), c);
    g_signal_connect(G_OBJECT(c->web_view), "decide-policy",
                     G_CALLBACK(decide_policy), NULL);
    g_signal_connect(G_OBJECT(c->web_view), "key-press-event",
                     G_CALLBACK(key_common), c);
    g_signal_connect(G_OBJECT(c->web_view), "button-press-event",
                     G_CALLBACK(key_common), c);
    g_signal_connect(G_OBJECT(c->web_view), "scroll-event",
                     G_CALLBACK(key_common), c);
    g_signal_connect(G_OBJECT(c->web_view), "mouse-target-changed",
                     G_CALLBACK(hover_web_view), c);
    g_signal_connect(G_OBJECT(c->web_view), "web-process-crashed",
                     G_CALLBACK(crashed_web_view), c);

    if (!initial_wc_setup_done)
    {
        if (accepted_language[0] != NULL)
            webkit_web_context_set_preferred_languages(wc, accepted_language);

        g_signal_connect(G_OBJECT(wc), "download-started",
                         G_CALLBACK(download_handle_start), NULL);

        trust_user_certs(wc);

        initial_wc_setup_done = TRUE;
    }

    if (user_agent != NULL)
        g_object_set(G_OBJECT(webkit_web_view_get_settings(WEBKIT_WEB_VIEW(c->web_view))),
                     "user-agent", user_agent, NULL);

    if (enable_webgl)
        webkit_settings_set_enable_webgl(webkit_web_view_get_settings(WEBKIT_WEB_VIEW(c->web_view)), TRUE);

    c->location = gtk_entry_new();
    g_signal_connect(G_OBJECT(c->location), "key-press-event",
                     G_CALLBACK(key_location), c);

    c->vbox = gtk_box_new(GTK_ORIENTATION_VERTICAL, 0);
    gtk_box_pack_start(GTK_BOX(c->vbox), c->location, FALSE, FALSE, 0);
    gtk_box_pack_start(GTK_BOX(c->vbox), c->web_view, TRUE, TRUE, 0);

    gtk_container_add(GTK_CONTAINER(c->win), c->vbox);

    if (show)
        show_web_view(NULL, c);
    else
        g_signal_connect(G_OBJECT(c->web_view), "ready-to-show",
                         G_CALLBACK(show_web_view), c);

    if (uri != NULL)
    {
        f = ensure_uri_scheme(uri);
        webkit_web_view_load_uri(WEBKIT_WEB_VIEW(c->web_view), f);
        g_free(f);
    }

    clients++;

    return WEBKIT_WEB_VIEW(c->web_view);
}

WebKitWebView *
client_new_request(WebKitWebView *web_view,
                   WebKitNavigationAction *navigation_action, gpointer data)
{
    return client_new(NULL, web_view, FALSE);
}

gboolean
command_abort_load(struct Client *c, struct CommandArguments *a)
{
    const gchar *t;

    if (c == NULL)
        return FALSE;

    t = webkit_web_view_get_uri(WEBKIT_WEB_VIEW(c->web_view));
    gtk_entry_set_text(GTK_ENTRY(c->location), (t == NULL ? __NAME__ : t));
    webkit_web_view_stop_loading(WEBKIT_WEB_VIEW(c->web_view));
    gtk_entry_set_progress_fraction(GTK_ENTRY(c->location), 0);

    return TRUE;
}

gboolean
command_close(struct Client *c, struct CommandArguments *a)
{
    if (c == NULL)
        return FALSE;

    gtk_widget_destroy(c->win);

    return TRUE;
}

gboolean
command_download_manager_close(struct Client *c, struct CommandArguments *a)
{
    downloadmanager_delete(dm.win, NULL);

    return TRUE;
}

gboolean
command_download_manager_open(struct Client *c, struct CommandArguments *a)
{
    gtk_widget_show_all(dm.win);

    return TRUE;
}

gboolean
command_focus_input_box(struct Client *c, struct CommandArguments *a)
{
    if (c == NULL)
        return FALSE;

    gtk_widget_grab_focus(c->location);

    if (a->string != NULL)
    {
        gtk_entry_set_text(GTK_ENTRY(c->location), a->string);
        gtk_editable_set_position(GTK_EDITABLE(c->location), -1);
    }

    return TRUE;
}

gboolean
command_go_backward(struct Client *c, struct CommandArguments *a)
{
    if (c == NULL)
        return FALSE;

    webkit_web_view_go_back(WEBKIT_WEB_VIEW(c->web_view));

    return TRUE;
}

gboolean
command_go_forward(struct Client *c, struct CommandArguments *a)
{
    if (c == NULL)
        return FALSE;

    webkit_web_view_go_forward(WEBKIT_WEB_VIEW(c->web_view));

    return TRUE;
}

gboolean
command_go_uri(struct Client *c, struct CommandArguments *a)
{
    gchar *f;

    if (c == NULL || a == NULL || a->string == NULL)
        return FALSE;

    f = ensure_uri_scheme(a->string);
    webkit_web_view_load_uri(WEBKIT_WEB_VIEW(c->web_view), f);
    g_free(f);

    return TRUE;
}

gboolean
command_go_uri_new_window(struct Client *c, struct CommandArguments *a)
{
    gchar *f;

    if (a == NULL || a->string == NULL)
        return FALSE;

    f = ensure_uri_scheme(a->string);
    client_new(f, NULL, TRUE);
    g_free(f);

    return TRUE;
}

gboolean
command_reload(struct Client *c, struct CommandArguments *a)
{
    if (c == NULL)
        return FALSE;

    webkit_web_view_reload_bypass_cache(WEBKIT_WEB_VIEW(c->web_view));

    return TRUE;
}

gboolean
command_reload_user_certs(struct Client *c, struct CommandArguments *a)
{
    if (c == NULL)
        return FALSE;

    trust_user_certs(webkit_web_view_get_context(WEBKIT_WEB_VIEW(c->web_view)));

    return TRUE;
}

gboolean
command_search_backward(struct Client *c, struct CommandArguments *a)
{
    if (c == NULL)
        return FALSE;

    search(c, -1);

    return TRUE;
}

gboolean
command_search_forward(struct Client *c, struct CommandArguments *a)
{
    if (c == NULL)
        return FALSE;

    search(c, 1);

    return TRUE;
}

gboolean
command_search_new(struct Client *c, struct CommandArguments *a)
{
    if (c == NULL || a->string == NULL)
        return FALSE;

    g_free(search_text);
    search_text = g_strdup(a->string);
    search(c, 0);

    return TRUE;
}

gboolean
command_zoom_decrease(struct Client *c, struct CommandArguments *a)
{
    gdouble z;

    if (c == NULL)
        return FALSE;

    z = webkit_web_view_get_zoom_level(WEBKIT_WEB_VIEW(c->web_view));
    z -= 0.1;
    webkit_web_view_set_zoom_level(WEBKIT_WEB_VIEW(c->web_view), z);

    return TRUE;
}

gboolean
command_zoom_increase(struct Client *c, struct CommandArguments *a)
{
    gdouble z;

    if (c == NULL)
        return FALSE;

    z = webkit_web_view_get_zoom_level(WEBKIT_WEB_VIEW(c->web_view));
    z += 0.1;
    webkit_web_view_set_zoom_level(WEBKIT_WEB_VIEW(c->web_view), z);

    return TRUE;
}

gboolean
command_zoom_reset(struct Client *c, struct CommandArguments *a)
{
    if (c == NULL)
        return FALSE;

    webkit_web_view_set_zoom_level(WEBKIT_WEB_VIEW(c->web_view), global_zoom);

    return TRUE;
}

void
cooperation_setup(void)
{
    GIOChannel *towatch;
    gchar *fifofilename, *fifopath;

    fifofilename = g_strdup_printf("%s-%s", __NAME__".fifo", fifo_suffix);
    fifopath = g_build_filename(g_get_user_runtime_dir(), fifofilename, NULL);
    g_free(fifofilename);

    if (!g_file_test(fifopath, G_FILE_TEST_EXISTS))
        mkfifo(fifopath, 0600);

    cooperative_pipe_fp = open(fifopath, O_WRONLY | O_NONBLOCK);
    if (!cooperative_pipe_fp)
    {
        fprintf(stderr, __NAME__": Can't open FIFO at all.\n");
    }
    else
    {
        if (write(cooperative_pipe_fp, "", 0) == -1)
        {
            /* Could not do an empty write to the FIFO which means there's
             * no one listening. */
            close(cooperative_pipe_fp);
            towatch = g_io_channel_new_file(fifopath, "r+", NULL);
            g_io_add_watch(towatch, G_IO_IN, (GIOFunc)remote_msg, NULL);
        }
        else
            cooperative_alone = FALSE;
    }

    g_free(fifopath);
}

void
changed_download_progress(GObject *obj, GParamSpec *pspec, gpointer data)
{
    WebKitDownload *download = WEBKIT_DOWNLOAD(obj);
    WebKitURIResponse *resp;
    GtkToolItem *tb = GTK_TOOL_ITEM(data);
    gdouble p, size_mb;
    const gchar *uri;
    gchar *t, *filename, *base;

    p = webkit_download_get_estimated_progress(download);
    p = p > 1 ? 1 : p;
    p = p < 0 ? 0 : p;
    p *= 100;
    resp = webkit_download_get_response(download);
    size_mb = webkit_uri_response_get_content_length(resp) / 1e6;

    uri = webkit_download_get_destination(download);
    filename = g_filename_from_uri(uri, NULL, NULL);
    if (filename == NULL)
    {
        /* This really should not happen because WebKit uses that URI to
         * write to a file... */
        fprintf(stderr, __NAME__": Could not construct file name from URI!\n");
        t = g_strdup_printf("%s (%.0f%% of %.1f MB)",
                            webkit_uri_response_get_uri(resp), p, size_mb);
    }
    else
    {
        base = g_path_get_basename(filename);
        t = g_strdup_printf("%s (%.0f%% of %.1f MB)", base, p, size_mb);
        g_free(filename);
        g_free(base);
    }
    gtk_tool_button_set_label(GTK_TOOL_BUTTON(tb), t);
    g_free(t);
}

void
changed_load_progress(GObject *obj, GParamSpec *pspec, gpointer data)
{
    struct Client *c = (struct Client *)data;
    gdouble p;

    p = webkit_web_view_get_estimated_load_progress(WEBKIT_WEB_VIEW(c->web_view));
    if (p == 1)
        p = 0;
    gtk_entry_set_progress_fraction(GTK_ENTRY(c->location), p);
}

void
changed_title(GObject *obj, GParamSpec *pspec, gpointer data)
{
    const gchar *t, *u;
    struct Client *c = (struct Client *)data;

    u = webkit_web_view_get_uri(WEBKIT_WEB_VIEW(c->web_view));
    t = webkit_web_view_get_title(WEBKIT_WEB_VIEW(c->web_view));

    u = u == NULL ? __NAME__ : u;
    u = u[0] == 0 ? __NAME__ : u;

    t = t == NULL ? u : t;
    t = t[0] == 0 ? u : t;

    gtk_window_set_title(GTK_WINDOW(c->win), t);
}

void
changed_uri(GObject *obj, GParamSpec *pspec, gpointer data)
{
    const gchar *t;
    struct Client *c = (struct Client *)data;
    FILE *fp;

    t = webkit_web_view_get_uri(WEBKIT_WEB_VIEW(c->web_view));

    /* When a web process crashes, we get a "notify::uri" signal, but we
     * can no longer read a meaningful URI. It's just an empty string
     * now. Not updating the location bar in this scenario is important,
     * because we would override the "WEB PROCESS CRASHED" message. */
    if (t != NULL && strlen(t) > 0)
    {
        gtk_entry_set_text(GTK_ENTRY(c->location), t);

        if (history_file != NULL)
        {
            fp = fopen(history_file, "a");
            if (fp != NULL)
            {
                fprintf(fp, "%s\n", t);
                fclose(fp);
            }
            else
                perror(__NAME__": Error opening history file");
        }
    }
}

gboolean
crashed_web_view(WebKitWebView *web_view, gpointer data)
{
    gchar *t;
    struct Client *c = (struct Client *)data;

    t = g_strdup_printf("WEB PROCESS CRASHED: %s",
                        webkit_web_view_get_uri(WEBKIT_WEB_VIEW(web_view)));
    gtk_entry_set_text(GTK_ENTRY(c->location), t);
    g_free(t);

    return TRUE;
}

gboolean
decide_policy(WebKitWebView *web_view, WebKitPolicyDecision *decision,
              WebKitPolicyDecisionType type, gpointer data)
{
    WebKitResponsePolicyDecision *r;

    switch (type)
    {
        case WEBKIT_POLICY_DECISION_TYPE_RESPONSE:
            r = WEBKIT_RESPONSE_POLICY_DECISION(decision);
            if (!webkit_response_policy_decision_is_mime_type_supported(r))
                webkit_policy_decision_download(decision);
            else
                webkit_policy_decision_use(decision);
            break;
        default:
            /* Use whatever default there is. */
            return FALSE;
    }
    return TRUE;
}

void
download_handle_finished(WebKitDownload *download, gpointer data)
{
    downloads--;
}

void
download_handle_start(WebKitWebView *web_view, WebKitDownload *download,
                      gpointer data)
{
    g_signal_connect(G_OBJECT(download), "decide-destination",
                     G_CALLBACK(download_handle), data);
}

gboolean
download_handle(WebKitDownload *download, gchar *suggested_filename, gpointer data)
{
    gchar *sug_clean, *path, *path2 = NULL, *uri;
    GtkToolItem *tb;
    int suffix = 1;
    size_t i;

    sug_clean = g_strdup(suggested_filename);
    for (i = 0; i < strlen(sug_clean); i++)
        if (sug_clean[i] == G_DIR_SEPARATOR)
            sug_clean[i] = '_';

    path = g_build_filename(download_dir, sug_clean, NULL);
    path2 = g_strdup(path);
    while (g_file_test(path2, G_FILE_TEST_EXISTS) && suffix < 1000)
    {
        g_free(path2);

        path2 = g_strdup_printf("%s.%d", path, suffix);
        suffix++;
    }

    if (suffix == 1000)
    {
        fprintf(stderr, __NAME__": Suffix reached limit for download.\n");
        webkit_download_cancel(download);
    }
    else
    {
        uri = g_filename_to_uri(path2, NULL, NULL);
        webkit_download_set_destination(download, uri);
        g_free(uri);

        tb = gtk_tool_button_new(NULL, NULL);
        gtk_tool_button_set_icon_name(GTK_TOOL_BUTTON(tb), "gtk-delete");
        gtk_tool_button_set_label(GTK_TOOL_BUTTON(tb), sug_clean);
        gtk_toolbar_insert(GTK_TOOLBAR(dm.toolbar), tb, 0);
        gtk_widget_show_all(dm.win);

        g_signal_connect(G_OBJECT(download), "notify::estimated-progress",
                         G_CALLBACK(changed_download_progress), tb);

        downloads++;
        g_signal_connect(G_OBJECT(download), "finished",
                         G_CALLBACK(download_handle_finished), NULL);

        g_object_ref(download);
        g_signal_connect(G_OBJECT(tb), "clicked",
                         G_CALLBACK(downloadmanager_cancel), download);
    }

    g_free(sug_clean);
    g_free(path);
    g_free(path2);

    /* Propagate -- to whom it may concern. */
    return FALSE;
}

void
downloadmanager_cancel(GtkToolButton *tb, gpointer data)
{
    WebKitDownload *download = WEBKIT_DOWNLOAD(data);

    webkit_download_cancel(download);
    g_object_unref(download);

    gtk_widget_destroy(GTK_WIDGET(tb));
}

gboolean
downloadmanager_delete(GtkWidget *obj, gpointer data)
{
    if (!quit_if_nothing_active())
        gtk_widget_hide(dm.win);

    return TRUE;
}

void
downloadmanager_setup(void)
{
    dm.win = gtk_window_new(GTK_WINDOW_TOPLEVEL);
    gtk_window_set_type_hint(GTK_WINDOW(dm.win), GDK_WINDOW_TYPE_HINT_DIALOG);
    gtk_window_set_default_size(GTK_WINDOW(dm.win), 500, 250);
    gtk_window_set_title(GTK_WINDOW(dm.win), __NAME__" - Download Manager");
    g_signal_connect(G_OBJECT(dm.win), "delete-event",
                     G_CALLBACK(downloadmanager_delete), NULL);
    g_signal_connect(G_OBJECT(dm.win), "key-press-event",
                     G_CALLBACK(key_common), NULL);

    dm.toolbar = gtk_toolbar_new();
    gtk_orientable_set_orientation(GTK_ORIENTABLE(dm.toolbar),
                                   GTK_ORIENTATION_VERTICAL);
    gtk_toolbar_set_style(GTK_TOOLBAR(dm.toolbar), GTK_TOOLBAR_BOTH_HORIZ);
    gtk_toolbar_set_show_arrow(GTK_TOOLBAR(dm.toolbar), FALSE);

    dm.scroll = gtk_scrolled_window_new(NULL, NULL);
    gtk_scrolled_window_set_policy(GTK_SCROLLED_WINDOW(dm.scroll),
                                   GTK_POLICY_AUTOMATIC, GTK_POLICY_AUTOMATIC);
    gtk_container_add(GTK_CONTAINER(dm.scroll), dm.toolbar);

    gtk_container_add(GTK_CONTAINER(dm.win), dm.scroll);
}

gchar *
ensure_uri_scheme(const gchar *t)
{
    gchar *f, *fabs;

    f = g_ascii_strdown(t, -1);
    if (!g_str_has_prefix(f, "http:") &&
        !g_str_has_prefix(f, "https:") &&
        !g_str_has_prefix(f, "file:") &&
        !g_str_has_prefix(f, "about:"))
    {
        g_free(f);
        fabs = realpath(t, NULL);
        if (fabs != NULL)
        {
            f = g_strdup_printf("file://%s", fabs);
            free(fabs);
        }
        else
            f = g_strdup_printf("http://%s", t);
        return f;
    }
    else
        return g_strdup(t);
}

void
grab_environment_configuration(void)
{
    const gchar *e;

    e = g_getenv(__NAME_UPPERCASE__"_ACCEPTED_LANGUAGE");
    if (e != NULL)
        accepted_language[0] = g_strdup(e);

    e = g_getenv(__NAME_UPPERCASE__"_DOWNLOAD_DIR");
    if (e != NULL)
        download_dir = g_strdup(e);

    e = g_getenv(__NAME_UPPERCASE__"_ENABLE_EXPERIMENTAL_WEBGL");
    if (e != NULL)
        enable_webgl = TRUE;

    e = g_getenv(__NAME_UPPERCASE__"_FIFO_SUFFIX");
    if (e != NULL)
        fifo_suffix = g_strdup(e);

    e = g_getenv(__NAME_UPPERCASE__"_HISTORY_FILE");
    if (e != NULL)
        history_file = g_strdup(e);

    e = g_getenv(__NAME_UPPERCASE__"_SEARCH_PREFIX");
    if (e != NULL)
        search_prefix = g_strdup(e);

    e = g_getenv(__NAME_UPPERCASE__"_USER_AGENT");
    if (e != NULL)
        user_agent = g_strdup(e);

    e = g_getenv(__NAME_UPPERCASE__"_ZOOM");
    if (e != NULL)
        global_zoom = atof(e);
}

void
hover_web_view(WebKitWebView *web_view, WebKitHitTestResult *ht, guint modifiers,
               gpointer data)
{
    struct Client *c = (struct Client *)data;

    if (!gtk_widget_is_focus(c->location))
    {
        if (webkit_hit_test_result_context_is_link(ht))
        {
            gtk_entry_set_text(GTK_ENTRY(c->location),
                               webkit_hit_test_result_get_link_uri(ht));

            g_free(c->hover_uri);
            c->hover_uri = g_strdup(webkit_hit_test_result_get_link_uri(ht));
        }
        else
        {
            gtk_entry_set_text(GTK_ENTRY(c->location),
                               webkit_web_view_get_uri(WEBKIT_WEB_VIEW(c->web_view)));

            g_free(c->hover_uri);
            c->hover_uri = NULL;
        }
    }
}

gchar *
human_event(GdkEvent *event)
{
    GdkEventButton *evb;
    GdkEventKey *evk;
    GdkEventScroll *evs;
    gdouble dx, dy;

    if (event->type == GDK_KEY_PRESS)
    {
        evk = (GdkEventKey *)event;
        return g_strdup_printf("%s%s%s%s",
                               evk->state & GDK_CONTROL_MASK ? "C-" : "",
                               evk->state & GDK_MOD1_MASK ? "M-" : "",
                               evk->state & GDK_SUPER_MASK ? "S-" : "",
                               gdk_keyval_name(evk->keyval));
    }
    else if (event->type == GDK_BUTTON_PRESS)
    {
        evb = (GdkEventButton *)event;
        return g_strdup_printf("%s%s%s%d",
                               evb->state & GDK_CONTROL_MASK ? "C-" : "",
                               evb->state & GDK_MOD1_MASK ? "M-" : "",
                               evb->state & GDK_SUPER_MASK ? "S-" : "",
                               evb->button);
    }
    else if (event->type == GDK_SCROLL)
    {
        evs = (GdkEventScroll *)event;
        gdk_event_get_scroll_deltas(event, &dx, &dy);
        return g_strdup_printf("%s%s%s%s",
                               evs->state & GDK_CONTROL_MASK ? "C-" : "",
                               evs->state & GDK_MOD1_MASK ? "M-" : "",
                               evs->state & GDK_SUPER_MASK ? "S-" : "",
                               dx != 0 ? (dx < 0 ? "x" : "X") :
                                         (dy < 0 ? "y" : "Y"));
    }

    return g_strdup("<unexpected event type>");
}

gboolean
input_driver(struct Client *c, gchar *context, gchar *key, const gchar *t)
{
    gchar *output = NULL, *uri_nc = NULL;
    gboolean handled = FALSE;

    if (!input_driver_run_if_needed())
    {
        fprintf(stderr, __NAME__": Fatal: Input driver not running\n");
        return FALSE;
    }

    write(indriv_stdin, "context\n", strlen("context\n"));
    write(indriv_stdin, context, strlen(context));
    write(indriv_stdin, "\n", 1);

    if (t != NULL)
    {
        write(indriv_stdin, "context_specific_text\n", strlen("context_specific_text\n"));
        write(indriv_stdin, t, strlen(t));
        write(indriv_stdin, "\n", 1);
    }

    if (c != NULL)
    {
        uri_nc = g_strdup(webkit_web_view_get_uri(WEBKIT_WEB_VIEW(c->web_view)));
        write(indriv_stdin, "current_uri\n", strlen("current_uri\n"));
        write(indriv_stdin, uri_nc, strlen(uri_nc));
        write(indriv_stdin, "\n", 1);
        g_free(uri_nc);
    }

    if (key != NULL)
    {
        write(indriv_stdin, "key\n", strlen("key\n"));
        write(indriv_stdin, key, strlen(key));
        write(indriv_stdin, "\n", 1);
    }

    if (c != NULL && c->hover_uri != NULL)
    {
        write(indriv_stdin, "hover_uri\n", strlen("hover_uri\n"));
        write(indriv_stdin, c->hover_uri, strlen(c->hover_uri));
        write(indriv_stdin, "\n", 1);
    }

    write(indriv_stdin, "execute\n", strlen("execute\n"));

    g_io_channel_read_line(indriv_stdout_channel, &output, NULL, NULL, NULL);
    handled = input_driver_execute_command(output, c);
    g_free(output);

    return handled;
}

gboolean
input_driver_context_menu(GtkAction *action, gpointer data)
{
    struct Client *c = (struct Client *)data;

    return input_driver(c, "handle_context_menu_uri", NULL,
                        c->context_menu_uri);
}

gboolean
input_driver_execute_command(gchar *line, struct Client *c)
{
    gchar **tokens = NULL;
    struct CommandArguments args = {0};
    gboolean (*fn_ptr)(struct Client *, struct CommandArguments *a);
    gboolean handled = FALSE;

    if (line != NULL)
    {
        tokens = g_strsplit(g_strstrip(line), " ", 2);
        if (tokens[0] != NULL)
        {
            if (strncmp(tokens[0], "nop", 3) == 0)
            {
                /* The driver might print "nop" to indicate that it did
                 * do something and that we should not deliver this
                 * event to Gtk or WebKit. */
                handled = TRUE;
            }
            else
            {
                fn_ptr = g_hash_table_lookup(command_hash, tokens[0]);
                if (fn_ptr != NULL)
                {
                    /* tokens[1] is either the second token or the NULL
                     * terminator of that list, which is fine. */
                    args.string = tokens[1];
                    handled = (*fn_ptr)(c, &args);
                }
            }
        }
    }

    g_strfreev(tokens);
    return handled;
}

gboolean
input_driver_run_if_needed(void)
{
    gint child_stdout;
    GError *err = NULL;
    GSpawnFlags flags;
    char *argv[] = { "lariza-input-driver", NULL };

    /* Launch new process if needed. Note that it's perfectly valid for
     * input drivers to quit after each request, even though they
     * *SHOULD* not do that for performance reasons.
     *
     * Anyway, we have to check if the process is still alive. It's not
     * a fatal error if it isn't because it might have simply crashed:
     * It's a user-supplied script and users are expected to hack on
     * that script, so that's just fine. */

    if (indriv_pid == -1 || waitpid(indriv_pid, NULL, WNOHANG) > 0)
    {
        /* Clean up previous resources. */
        if (indriv_stdout_channel != NULL)
            g_io_channel_shutdown(indriv_stdout_channel, FALSE, NULL);

        if (indriv_stdin != -1)
            close(indriv_stdin);

        fprintf(stderr, __NAME__": Launching new input driver\n");

        /* Spawn new child with new resources. */
        flags = G_SPAWN_DO_NOT_REAP_CHILD | G_SPAWN_SEARCH_PATH;
        if (!g_spawn_async_with_pipes(NULL, argv, NULL, flags, NULL, NULL,
                                      &indriv_pid, &indriv_stdin, &child_stdout,
                                      NULL, &err))
        {
            fprintf(stderr, __NAME__": Fatal: Could not launch input driver: %s\n", err->message);
            g_error_free(err);
            return FALSE;
        }

        indriv_stdout_channel = g_io_channel_unix_new(child_stdout);
        if (indriv_stdout_channel == NULL)
        {
            fprintf(stderr, __NAME__": Fatal: Could open input driver's stdout\n");
            return FALSE;
        }
    }

    return TRUE;
}

gboolean
key_common(GtkWidget *widget, GdkEvent *event, gpointer data)
{
    struct Client *c = (struct Client *)data;
    gchar *k, *context = NULL;
    gboolean handled;

    /* XXX There's something odd happening here with key events.
     *
     * If we don't return TRUE from this function (which we only should
     * do if we want to prevent this event from being propagated to
     * other handlers -- we only want that if input_handler() returns
     * TRUE), then we get duplicate events. It's not the exact same
     * event, it has a different address. But all values are identical.
     * This results in the input driver being spawned twice which is
     * kind of annoying.
     *
     * This has nothing to do with the input driver's new code. This
     * behaviour can be seen in older versions of lariza as well.
     *
     * Backtraces in GDB indicate that one event comes from
     * WTF::RunLoop::performWork(), the other one doesn't. */

    /* For performance reasons, we only report scroll events if a
     * modifier key has been pressed as well. */

    if (event->type == GDK_KEY_PRESS)
        context = "hid_key";
    else if (event->type == GDK_BUTTON_PRESS)
        context = "hid_button";
    else if (event->type == GDK_SCROLL &&
             (
              ((GdkEventScroll *)event)->state & GDK_CONTROL_MASK ||
              ((GdkEventScroll *)event)->state & GDK_MOD1_MASK ||
              ((GdkEventScroll *)event)->state & GDK_SUPER_MASK
             )
            )
        context = "hid_scroll";

    if (context != NULL)
    {
        k = human_event(event);
        handled = input_driver(c, context, k, NULL);
        g_free(k);
        return handled;
    }

    return FALSE;
}

gboolean
key_location(GtkWidget *widget, GdkEvent *event, gpointer data)
{
    struct Client *c = (struct Client *)data;
    const gchar *t;

    if (key_common(widget, event, data))
        return TRUE;

    if (event->type == GDK_KEY_PRESS)
    {
        switch (((GdkEventKey *)event)->keyval)
        {
            case GDK_KEY_KP_Enter:
            case GDK_KEY_Return:
                gtk_widget_grab_focus(c->web_view);
                t = gtk_entry_get_text(GTK_ENTRY(c->location));
                input_driver(c, "inputbox", NULL, t);
                return TRUE;
        }
    }

    return FALSE;
}

void
load_command_hash(void)
{
    command_hash = g_hash_table_new(g_str_hash, g_str_equal);
    g_hash_table_insert(command_hash, "abort_load", command_abort_load);
    g_hash_table_insert(command_hash, "close", command_close);
    g_hash_table_insert(command_hash, "download_manager_close", command_download_manager_close);
    g_hash_table_insert(command_hash, "download_manager_open", command_download_manager_open);
    g_hash_table_insert(command_hash, "focus_input_box", command_focus_input_box);
    g_hash_table_insert(command_hash, "go_backward", command_go_backward);
    g_hash_table_insert(command_hash, "go_forward", command_go_forward);
    g_hash_table_insert(command_hash, "go_uri", command_go_uri);
    g_hash_table_insert(command_hash, "go_uri_new_window", command_go_uri_new_window);
    g_hash_table_insert(command_hash, "reload_page", command_reload);
    g_hash_table_insert(command_hash, "reload_user_certs", command_reload_user_certs);
    g_hash_table_insert(command_hash, "search_backward", command_search_backward);
    g_hash_table_insert(command_hash, "search_forward", command_search_forward);
    g_hash_table_insert(command_hash, "search_new", command_search_new);
    g_hash_table_insert(command_hash, "zoom_decrease", command_zoom_decrease);
    g_hash_table_insert(command_hash, "zoom_increase", command_zoom_increase);
    g_hash_table_insert(command_hash, "zoom_reset", command_zoom_reset);
}

gboolean
menu_web_view(WebKitWebView *web_view, WebKitContextMenu *menu, GdkEvent *ev,
              WebKitHitTestResult *ht, gpointer data)
{
    struct Client *c = (struct Client *)data;
    GtkAction *action = NULL;
    WebKitContextMenuItem *mi = NULL;
    const gchar *uri = NULL;

    (void)ev;

    if (webkit_hit_test_result_context_is_link(ht))
        uri = webkit_hit_test_result_get_link_uri(ht);
    else if (webkit_hit_test_result_context_is_image(ht))
        uri = webkit_hit_test_result_get_image_uri(ht);
    else if (webkit_hit_test_result_context_is_media(ht))
        uri = webkit_hit_test_result_get_media_uri(ht);

    if (uri != NULL)
    {
        webkit_context_menu_append(menu, webkit_context_menu_item_new_separator());

        if (c->context_menu_uri != NULL)
            g_free(c->context_menu_uri);
        c->context_menu_uri = g_strdup(uri);
        action = gtk_action_new("external_handler", "Open with external handler",
                                NULL, NULL);
        g_signal_connect(G_OBJECT(action), "activate",
                         G_CALLBACK(input_driver_context_menu), data);
        mi = webkit_context_menu_item_new(action);
        webkit_context_menu_append(menu, mi);
    }

    /* FALSE = Show the menu. (TRUE = Don't ever show it.) */
    return FALSE;
}

gboolean
quit_if_nothing_active(void)
{
    if (clients == 0)
    {
        if (downloads == 0)
        {
            gtk_main_quit();
            return TRUE;
        }
        else
            gtk_widget_show_all(dm.win);
    }

    return FALSE;
}

gboolean
remote_msg(GIOChannel *channel, GIOCondition condition, gpointer data)
{
    gchar *line = NULL;

    g_io_channel_read_line(channel, &line, NULL, NULL, NULL);
    input_driver_execute_command(line, NULL);

    return TRUE;
}

void
search(struct Client *c, gint direction)
{
    WebKitWebView *web_view = WEBKIT_WEB_VIEW(c->web_view);
    WebKitFindController *fc = webkit_web_view_get_find_controller(web_view);

    if (search_text == NULL)
        return;

    switch (direction)
    {
        case 0:
            webkit_find_controller_search(fc, search_text,
                                          WEBKIT_FIND_OPTIONS_CASE_INSENSITIVE |
                                          WEBKIT_FIND_OPTIONS_WRAP_AROUND,
                                          G_MAXUINT);
            break;
        case 1:
            webkit_find_controller_search_next(fc);
            break;
        case -1:
            webkit_find_controller_search_previous(fc);
            break;
    }
}

void
show_web_view(WebKitWebView *web_view, gpointer data)
{
    struct Client *c = (struct Client *)data;

    (void)web_view;

    gtk_widget_grab_focus(c->web_view);
    gtk_widget_show_all(c->win);
}

Window
tabbed_launch(void)
{
    gint tabbed_stdout;
    GIOChannel *tabbed_stdout_channel;
    GError *err = NULL;
    gchar *output = NULL;
    char *argv[] = { "tabbed", "-c", "-d", "-p", "s1", "-n", __NAME__, NULL };
    Window plug_into;

    if (!g_spawn_async_with_pipes(NULL, argv, NULL, G_SPAWN_SEARCH_PATH, NULL,
                                  NULL, NULL, NULL, &tabbed_stdout, NULL,
                                  &err))
    {
        fprintf(stderr, __NAME__": Could not launch tabbed: %s\n", err->message);
        g_error_free(err);
        return 0;
    }

    tabbed_stdout_channel = g_io_channel_unix_new(tabbed_stdout);
    if (tabbed_stdout_channel == NULL)
    {
        fprintf(stderr, __NAME__": Could open tabbed's stdout\n");
        return 0;
    }
    g_io_channel_read_line(tabbed_stdout_channel, &output, NULL, NULL, NULL);
    g_io_channel_shutdown(tabbed_stdout_channel, FALSE, NULL);
    if (output == NULL)
    {
        fprintf(stderr, __NAME__": Could not read XID from tabbed\n");
        return 0;
    }
    g_strstrip(output);
    plug_into = strtol(output, NULL, 16);
    g_free(output);
    if (plug_into == 0)
        fprintf(stderr, __NAME__": The XID from tabbed is 0\n");
    return plug_into;
}

void
trust_user_certs(WebKitWebContext *wc)
{
    GTlsCertificate *cert;
    const gchar *basedir, *file, *absfile;
    GDir *dir;

    basedir = g_build_filename(g_get_user_config_dir(), __NAME__, "certs", NULL);
    dir = g_dir_open(basedir, 0, NULL);
    if (dir != NULL)
    {
        file = g_dir_read_name(dir);
        while (file != NULL)
        {
            absfile = g_build_filename(g_get_user_config_dir(), __NAME__, "certs",
                                       file, NULL);
            cert = g_tls_certificate_new_from_file(absfile, NULL);
            if (cert == NULL)
                fprintf(stderr, __NAME__": Could not load trusted cert '%s'\n", file);
            else
                webkit_web_context_allow_tls_certificate_for_host(wc, cert, file);
            file = g_dir_read_name(dir);
        }
        g_dir_close(dir);
    }
}


int
main(int argc, char **argv)
{
    gchar *c;
    int opt, i;

    gtk_init(&argc, &argv);
    webkit_web_context_set_process_model(webkit_web_context_get_default(),
        WEBKIT_PROCESS_MODEL_MULTIPLE_SECONDARY_PROCESSES);

    load_command_hash();
    grab_environment_configuration();

    while ((opt = getopt(argc, argv, "e:CT")) != -1)
    {
        switch (opt)
        {
            case 'e':
                embed = atol(optarg);
                tabbed_automagic = FALSE;
                break;
            case 'C':
                cooperative_instances = FALSE;
                break;
            case 'T':
                tabbed_automagic = FALSE;
                break;
            default:
                fprintf(stderr, "Usage: "__NAME__" [OPTION]... [URI]...\n");
                exit(EXIT_FAILURE);
        }
    }

    if (cooperative_instances)
        cooperation_setup();
    downloadmanager_setup();

    if (tabbed_automagic && !(cooperative_instances && !cooperative_alone))
        embed = tabbed_launch();

    if (!cooperative_instances || cooperative_alone)
    {
        c = g_build_filename(g_get_user_config_dir(), __NAME__, "web_extensions",
                             NULL);
        webkit_web_context_set_web_extensions_directory(
            webkit_web_context_get_default(), c
        );
    }

    if (optind >= argc)
        client_new("about:blank", NULL, TRUE);
    else
    {
        for (i = optind; i < argc; i++)
            client_new(argv[i], NULL, TRUE);
    }

    if (!cooperative_instances || cooperative_alone)
        gtk_main();
    exit(EXIT_SUCCESS);
}
