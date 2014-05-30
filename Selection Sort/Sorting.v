




<!DOCTYPE html>
<html class="   ">
  <head prefix="og: http://ogp.me/ns# fb: http://ogp.me/ns/fb# object: http://ogp.me/ns/object# article: http://ogp.me/ns/article# profile: http://ogp.me/ns/profile#">
    <meta charset='utf-8'>
    <meta http-equiv="X-UA-Compatible" content="IE=edge">
    
    
    <title>lvr-coq/Sorting.v at master · andrejbauer/lvr-coq · GitHub</title>
    <link rel="search" type="application/opensearchdescription+xml" href="/opensearch.xml" title="GitHub" />
    <link rel="fluid-icon" href="https://github.com/fluidicon.png" title="GitHub" />
    <link rel="apple-touch-icon" sizes="57x57" href="/apple-touch-icon-114.png" />
    <link rel="apple-touch-icon" sizes="114x114" href="/apple-touch-icon-114.png" />
    <link rel="apple-touch-icon" sizes="72x72" href="/apple-touch-icon-144.png" />
    <link rel="apple-touch-icon" sizes="144x144" href="/apple-touch-icon-144.png" />
    <meta property="fb:app_id" content="1401488693436528"/>

      <meta content="@github" name="twitter:site" /><meta content="summary" name="twitter:card" /><meta content="andrejbauer/lvr-coq" name="twitter:title" /><meta content="lvr-coq - Coq related material for the Logic in computer science course" name="twitter:description" /><meta content="https://avatars3.githubusercontent.com/u/646599?s=400" name="twitter:image:src" />
<meta content="GitHub" property="og:site_name" /><meta content="object" property="og:type" /><meta content="https://avatars3.githubusercontent.com/u/646599?s=400" property="og:image" /><meta content="andrejbauer/lvr-coq" property="og:title" /><meta content="https://github.com/andrejbauer/lvr-coq" property="og:url" /><meta content="lvr-coq - Coq related material for the Logic in computer science course" property="og:description" />

    <link rel="assets" href="https://assets-cdn.github.com/">
    <link rel="conduit-xhr" href="https://ghconduit.com:25035/">
    

    <meta name="msapplication-TileImage" content="/windows-tile.png" />
    <meta name="msapplication-TileColor" content="#ffffff" />
    <meta name="selected-link" value="repo_source" data-pjax-transient />
      <meta name="google-analytics" content="UA-3769691-2">

    <meta content="collector.githubapp.com" name="octolytics-host" /><meta content="collector-cdn.github.com" name="octolytics-script-host" /><meta content="github" name="octolytics-app-id" /><meta content="C1025603:089F:D323F56:538849EF" name="octolytics-dimension-request_id" />
    

    
    
    <link rel="icon" type="image/x-icon" href="https://assets-cdn.github.com/favicon.ico" />


    <meta content="authenticity_token" name="csrf-param" />
<meta content="JZzn7xH7uRLbBAPehYid+CqHGNb3+jQ9TxwqpDCK3xtBbzJcrJI7DWUQxKdP4gTlfQmgv7uc8YBhS26GTpLzdQ==" name="csrf-token" />

    <link href="https://assets-cdn.github.com/assets/github-382e2d2394fe36287509f9d88e1aae81a78b71b2.css" media="all" rel="stylesheet" type="text/css" />
    <link href="https://assets-cdn.github.com/assets/github2-700c786303eff465608cf2e6e32e27d636038f05.css" media="all" rel="stylesheet" type="text/css" />
    


    <meta http-equiv="x-pjax-version" content="367b402e0291706cc3bfccf2d324be4b">

      
  <meta name="description" content="lvr-coq - Coq related material for the Logic in computer science course" />

  <meta content="646599" name="octolytics-dimension-user_id" /><meta content="andrejbauer" name="octolytics-dimension-user_login" /><meta content="18590445" name="octolytics-dimension-repository_id" /><meta content="andrejbauer/lvr-coq" name="octolytics-dimension-repository_nwo" /><meta content="true" name="octolytics-dimension-repository_public" /><meta content="false" name="octolytics-dimension-repository_is_fork" /><meta content="18590445" name="octolytics-dimension-repository_network_root_id" /><meta content="andrejbauer/lvr-coq" name="octolytics-dimension-repository_network_root_nwo" />
  <link href="https://github.com/andrejbauer/lvr-coq/commits/master.atom" rel="alternate" title="Recent Commits to lvr-coq:master" type="application/atom+xml" />

  </head>


  <body class="logged_out  env-production windows vis-public page-blob">
    <a href="#start-of-content" tabindex="1" class="accessibility-aid js-skip-to-content">Skip to content</a>
    <div class="wrapper">
      
      
      
      


      
      <div class="header header-logged-out">
  <div class="container clearfix">

    <a class="header-logo-wordmark" href="https://github.com/">
      <span class="mega-octicon octicon-logo-github"></span>
    </a>

    <div class="header-actions">
        <a class="button primary" href="/join">Sign up</a>
      <a class="button signin" href="/login?return_to=%2Fandrejbauer%2Flvr-coq%2Fblob%2Fmaster%2FSorting.v">Sign in</a>
    </div>

    <div class="command-bar js-command-bar  in-repository">

      <ul class="top-nav">
          <li class="explore"><a href="/explore">Explore</a></li>
        <li class="features"><a href="/features">Features</a></li>
          <li class="enterprise"><a href="https://enterprise.github.com/">Enterprise</a></li>
          <li class="blog"><a href="/blog">Blog</a></li>
      </ul>
        <form accept-charset="UTF-8" action="/search" class="command-bar-form" id="top_search_form" method="get">

<div class="commandbar">
  <span class="message"></span>
  <input type="text" data-hotkey="s" name="q" id="js-command-bar-field" placeholder="Search or type a command" tabindex="1" autocapitalize="off"
    
    
      data-repo="andrejbauer/lvr-coq"
      data-branch="master"
      data-sha="d5d700634b1e0d3558ec3527ce3be743f7c473a5"
  >
  <div class="display hidden"></div>
</div>

    <input type="hidden" name="nwo" value="andrejbauer/lvr-coq" />

    <div class="select-menu js-menu-container js-select-menu search-context-select-menu">
      <span class="minibutton select-menu-button js-menu-target" role="button" aria-haspopup="true">
        <span class="js-select-button">This repository</span>
      </span>

      <div class="select-menu-modal-holder js-menu-content js-navigation-container" aria-hidden="true">
        <div class="select-menu-modal">

          <div class="select-menu-item js-navigation-item js-this-repository-navigation-item selected">
            <span class="select-menu-item-icon octicon octicon-check"></span>
            <input type="radio" class="js-search-this-repository" name="search_target" value="repository" checked="checked" />
            <div class="select-menu-item-text js-select-button-text">This repository</div>
          </div> <!-- /.select-menu-item -->

          <div class="select-menu-item js-navigation-item js-all-repositories-navigation-item">
            <span class="select-menu-item-icon octicon octicon-check"></span>
            <input type="radio" name="search_target" value="global" />
            <div class="select-menu-item-text js-select-button-text">All repositories</div>
          </div> <!-- /.select-menu-item -->

        </div>
      </div>
    </div>

  <span class="help tooltipped tooltipped-s" aria-label="Show command bar help">
    <span class="octicon octicon-question"></span>
  </span>


  <input type="hidden" name="ref" value="cmdform">

</form>
    </div>

  </div>
</div>



      <div id="start-of-content" class="accessibility-aid"></div>
          <div class="site" itemscope itemtype="http://schema.org/WebPage">
    <div id="js-flash-container">
      
    </div>
    <div class="pagehead repohead instapaper_ignore readability-menu">
      <div class="container">
        

<ul class="pagehead-actions">


  <li>
    <a href="/login?return_to=%2Fandrejbauer%2Flvr-coq"
    class="minibutton with-count star-button tooltipped tooltipped-n"
    aria-label="You must be signed in to star a repository" rel="nofollow">
    <span class="octicon octicon-star"></span>Star
  </a>

    <a class="social-count js-social-count" href="/andrejbauer/lvr-coq/stargazers">
      0
    </a>

  </li>

    <li>
      <a href="/login?return_to=%2Fandrejbauer%2Flvr-coq"
        class="minibutton with-count js-toggler-target fork-button tooltipped tooltipped-n"
        aria-label="You must be signed in to fork a repository" rel="nofollow">
        <span class="octicon octicon-repo-forked"></span>Fork
      </a>
      <a href="/andrejbauer/lvr-coq/network" class="social-count">
        12
      </a>
    </li>
</ul>

        <h1 itemscope itemtype="http://data-vocabulary.org/Breadcrumb" class="entry-title public">
          <span class="repo-label"><span>public</span></span>
          <span class="mega-octicon octicon-repo"></span>
          <span class="author"><a href="/andrejbauer" class="url fn" itemprop="url" rel="author"><span itemprop="title">andrejbauer</span></a></span><!--
       --><span class="path-divider">/</span><!--
       --><strong><a href="/andrejbauer/lvr-coq" class="js-current-repository js-repo-home-link">lvr-coq</a></strong>

          <span class="page-context-loader">
            <img alt="" height="16" src="https://assets-cdn.github.com/images/spinners/octocat-spinner-32.gif" width="16" />
          </span>

        </h1>
      </div><!-- /.container -->
    </div><!-- /.repohead -->

    <div class="container">
      <div class="repository-with-sidebar repo-container new-discussion-timeline js-new-discussion-timeline  ">
        <div class="repository-sidebar clearfix">
            

<div class="sunken-menu vertical-right repo-nav js-repo-nav js-repository-container-pjax js-octicon-loaders">
  <div class="sunken-menu-contents">
    <ul class="sunken-menu-group">
      <li class="tooltipped tooltipped-w" aria-label="Code">
        <a href="/andrejbauer/lvr-coq" aria-label="Code" class="selected js-selected-navigation-item sunken-menu-item" data-hotkey="g c" data-pjax="true" data-selected-links="repo_source repo_downloads repo_commits repo_releases repo_tags repo_branches /andrejbauer/lvr-coq">
          <span class="octicon octicon-code"></span> <span class="full-word">Code</span>
          <img alt="" class="mini-loader" height="16" src="https://assets-cdn.github.com/images/spinners/octocat-spinner-32.gif" width="16" />
</a>      </li>

        <li class="tooltipped tooltipped-w" aria-label="Issues">
          <a href="/andrejbauer/lvr-coq/issues" aria-label="Issues" class="js-selected-navigation-item sunken-menu-item js-disable-pjax" data-hotkey="g i" data-selected-links="repo_issues /andrejbauer/lvr-coq/issues">
            <span class="octicon octicon-issue-opened"></span> <span class="full-word">Issues</span>
            <span class='counter'>0</span>
            <img alt="" class="mini-loader" height="16" src="https://assets-cdn.github.com/images/spinners/octocat-spinner-32.gif" width="16" />
</a>        </li>

      <li class="tooltipped tooltipped-w" aria-label="Pull Requests">
        <a href="/andrejbauer/lvr-coq/pulls" aria-label="Pull Requests" class="js-selected-navigation-item sunken-menu-item js-disable-pjax" data-hotkey="g p" data-selected-links="repo_pulls /andrejbauer/lvr-coq/pulls">
            <span class="octicon octicon-git-pull-request"></span> <span class="full-word">Pull Requests</span>
            <span class='counter'>0</span>
            <img alt="" class="mini-loader" height="16" src="https://assets-cdn.github.com/images/spinners/octocat-spinner-32.gif" width="16" />
</a>      </li>


    </ul>
    <div class="sunken-menu-separator"></div>
    <ul class="sunken-menu-group">

      <li class="tooltipped tooltipped-w" aria-label="Pulse">
        <a href="/andrejbauer/lvr-coq/pulse" aria-label="Pulse" class="js-selected-navigation-item sunken-menu-item" data-pjax="true" data-selected-links="pulse /andrejbauer/lvr-coq/pulse">
          <span class="octicon octicon-pulse"></span> <span class="full-word">Pulse</span>
          <img alt="" class="mini-loader" height="16" src="https://assets-cdn.github.com/images/spinners/octocat-spinner-32.gif" width="16" />
</a>      </li>

      <li class="tooltipped tooltipped-w" aria-label="Graphs">
        <a href="/andrejbauer/lvr-coq/graphs" aria-label="Graphs" class="js-selected-navigation-item sunken-menu-item" data-pjax="true" data-selected-links="repo_graphs repo_contributors /andrejbauer/lvr-coq/graphs">
          <span class="octicon octicon-graph"></span> <span class="full-word">Graphs</span>
          <img alt="" class="mini-loader" height="16" src="https://assets-cdn.github.com/images/spinners/octocat-spinner-32.gif" width="16" />
</a>      </li>

      <li class="tooltipped tooltipped-w" aria-label="Network">
        <a href="/andrejbauer/lvr-coq/network" aria-label="Network" class="js-selected-navigation-item sunken-menu-item js-disable-pjax" data-selected-links="repo_network /andrejbauer/lvr-coq/network">
          <span class="octicon octicon-repo-forked"></span> <span class="full-word">Network</span>
          <img alt="" class="mini-loader" height="16" src="https://assets-cdn.github.com/images/spinners/octocat-spinner-32.gif" width="16" />
</a>      </li>
    </ul>


  </div>
</div>

              <div class="only-with-full-nav">
                

  

<div class="clone-url open"
  data-protocol-type="http"
  data-url="/users/set_protocol?protocol_selector=http&amp;protocol_type=clone">
  <h3><strong>HTTPS</strong> clone URL</h3>
  <div class="clone-url-box">
    <input type="text" class="clone js-url-field"
           value="https://github.com/andrejbauer/lvr-coq.git" readonly="readonly">
    <span class="url-box-clippy">
    <button aria-label="copy to clipboard" class="js-zeroclipboard minibutton zeroclipboard-button" data-clipboard-text="https://github.com/andrejbauer/lvr-coq.git" data-copied-hint="copied!" type="button"><span class="octicon octicon-clippy"></span></button>
    </span>
  </div>
</div>

  

<div class="clone-url "
  data-protocol-type="subversion"
  data-url="/users/set_protocol?protocol_selector=subversion&amp;protocol_type=clone">
  <h3><strong>Subversion</strong> checkout URL</h3>
  <div class="clone-url-box">
    <input type="text" class="clone js-url-field"
           value="https://github.com/andrejbauer/lvr-coq" readonly="readonly">
    <span class="url-box-clippy">
    <button aria-label="copy to clipboard" class="js-zeroclipboard minibutton zeroclipboard-button" data-clipboard-text="https://github.com/andrejbauer/lvr-coq" data-copied-hint="copied!" type="button"><span class="octicon octicon-clippy"></span></button>
    </span>
  </div>
</div>


<p class="clone-options">You can clone with
      <a href="#" class="js-clone-selector" data-protocol="http">HTTPS</a>
      or <a href="#" class="js-clone-selector" data-protocol="subversion">Subversion</a>.
  <span class="help tooltipped tooltipped-n" aria-label="Get help on which URL is right for you.">
    <a href="https://help.github.com/articles/which-remote-url-should-i-use">
    <span class="octicon octicon-question"></span>
    </a>
  </span>
</p>


  <a href="http://windows.github.com" class="minibutton sidebar-button" title="Save andrejbauer/lvr-coq to your computer and use it in GitHub Desktop." aria-label="Save andrejbauer/lvr-coq to your computer and use it in GitHub Desktop.">
    <span class="octicon octicon-device-desktop"></span>
    Clone in Desktop
  </a>

                <a href="/andrejbauer/lvr-coq/archive/master.zip"
                   class="minibutton sidebar-button"
                   aria-label="Download andrejbauer/lvr-coq as a zip file"
                   title="Download andrejbauer/lvr-coq as a zip file"
                   rel="nofollow">
                  <span class="octicon octicon-cloud-download"></span>
                  Download ZIP
                </a>
              </div>
        </div><!-- /.repository-sidebar -->

        <div id="js-repo-pjax-container" class="repository-content context-loader-container" data-pjax-container>
          


<a href="/andrejbauer/lvr-coq/blob/172b99c443b85e981a6634374a26b473b2dc3cd8/Sorting.v" class="hidden js-permalink-shortcut" data-hotkey="y">Permalink</a>

<!-- blob contrib key: blob_contributors:v21:3b70adbe1c5d9c61444951e420064f91 -->

<p title="This is a placeholder element" class="js-history-link-replace hidden"></p>

<a href="/andrejbauer/lvr-coq/find/master" data-pjax data-hotkey="t" class="js-show-file-finder" style="display:none">Show File Finder</a>

<div class="file-navigation">
  

<div class="select-menu js-menu-container js-select-menu" >
  <span class="minibutton select-menu-button js-menu-target" data-hotkey="w"
    data-master-branch="master"
    data-ref="master"
    role="button" aria-label="Switch branches or tags" tabindex="0" aria-haspopup="true">
    <span class="octicon octicon-git-branch"></span>
    <i>branch:</i>
    <span class="js-select-button">master</span>
  </span>

  <div class="select-menu-modal-holder js-menu-content js-navigation-container" data-pjax aria-hidden="true">

    <div class="select-menu-modal">
      <div class="select-menu-header">
        <span class="select-menu-title">Switch branches/tags</span>
        <span class="octicon octicon-x js-menu-close"></span>
      </div> <!-- /.select-menu-header -->

      <div class="select-menu-filters">
        <div class="select-menu-text-filter">
          <input type="text" aria-label="Filter branches/tags" id="context-commitish-filter-field" class="js-filterable-field js-navigation-enable" placeholder="Filter branches/tags">
        </div>
        <div class="select-menu-tabs">
          <ul>
            <li class="select-menu-tab">
              <a href="#" data-tab-filter="branches" class="js-select-menu-tab">Branches</a>
            </li>
            <li class="select-menu-tab">
              <a href="#" data-tab-filter="tags" class="js-select-menu-tab">Tags</a>
            </li>
          </ul>
        </div><!-- /.select-menu-tabs -->
      </div><!-- /.select-menu-filters -->

      <div class="select-menu-list select-menu-tab-bucket js-select-menu-tab-bucket" data-tab-filter="branches">

        <div data-filterable-for="context-commitish-filter-field" data-filterable-type="substring">


            <div class="select-menu-item js-navigation-item selected">
              <span class="select-menu-item-icon octicon octicon-check"></span>
              <a href="/andrejbauer/lvr-coq/blob/master/Sorting.v"
                 data-name="master"
                 data-skip-pjax="true"
                 rel="nofollow"
                 class="js-navigation-open select-menu-item-text js-select-button-text css-truncate-target"
                 title="master">master</a>
            </div> <!-- /.select-menu-item -->
        </div>

          <div class="select-menu-no-results">Nothing to show</div>
      </div> <!-- /.select-menu-list -->

      <div class="select-menu-list select-menu-tab-bucket js-select-menu-tab-bucket" data-tab-filter="tags">
        <div data-filterable-for="context-commitish-filter-field" data-filterable-type="substring">


        </div>

        <div class="select-menu-no-results">Nothing to show</div>
      </div> <!-- /.select-menu-list -->

    </div> <!-- /.select-menu-modal -->
  </div> <!-- /.select-menu-modal-holder -->
</div> <!-- /.select-menu -->

  <div class="breadcrumb">
    <span class='repo-root js-repo-root'><span itemscope="" itemtype="http://data-vocabulary.org/Breadcrumb"><a href="/andrejbauer/lvr-coq" data-branch="master" data-direction="back" data-pjax="true" itemscope="url"><span itemprop="title">lvr-coq</span></a></span></span><span class="separator"> / </span><strong class="final-path">Sorting.v</strong> <button aria-label="copy to clipboard" class="js-zeroclipboard minibutton zeroclipboard-button" data-clipboard-text="Sorting.v" data-copied-hint="copied!" type="button"><span class="octicon octicon-clippy"></span></button>
  </div>
</div>


  <div class="commit file-history-tease">
      <img alt="Andrej Bauer" class="main-avatar js-avatar" data-user="646599" height="24" src="https://avatars0.githubusercontent.com/u/646599?s=140" width="24" />
      <span class="author"><a href="/andrejbauer" rel="author">andrejbauer</a></span>
      <time datetime="2014-05-30T10:18:32+02:00" is="relative-time">May 30, 2014</time>
      <div class="commit-title">
          <a href="/andrejbauer/lvr-coq/commit/172b99c443b85e981a6634374a26b473b2dc3cd8" class="message" data-pjax="true" title="Boljsi sorting">Boljsi sorting</a>
      </div>

    <div class="participation">
      <p class="quickstat"><a href="#blob_contributors_box" rel="facebox"><strong>1</strong>  contributor</a></p>
      
    </div>
    <div id="blob_contributors_box" style="display:none">
      <h2 class="facebox-header">Users who have contributed to this file</h2>
      <ul class="facebox-user-list">
          <li class="facebox-user-list-item">
            <img alt="Andrej Bauer" class=" js-avatar" data-user="646599" height="24" src="https://avatars0.githubusercontent.com/u/646599?s=140" width="24" />
            <a href="/andrejbauer">andrejbauer</a>
          </li>
      </ul>
    </div>
  </div>

<div class="file-box">
  <div class="file">
    <div class="meta clearfix">
      <div class="info file-name">
        <span class="icon"><b class="octicon octicon-file-text"></b></span>
        <span class="mode" title="File Mode">file</span>
        <span class="meta-divider"></span>
          <span>233 lines (199 sloc)</span>
          <span class="meta-divider"></span>
        <span>6.506 kb</span>
      </div>
      <div class="actions">
        <div class="button-group">
            <a class="minibutton tooltipped tooltipped-w"
               href="http://windows.github.com" aria-label="Open this file in GitHub for Windows">
                <span class="octicon octicon-device-desktop"></span> Open
            </a>
              <a class="minibutton disabled tooltipped tooltipped-w" href="#"
                 aria-label="You must be signed in to make or propose changes">Edit</a>
          <a href="/andrejbauer/lvr-coq/raw/master/Sorting.v" class="button minibutton " id="raw-url">Raw</a>
            <a href="/andrejbauer/lvr-coq/blame/master/Sorting.v" class="button minibutton js-update-url-with-hash">Blame</a>
          <a href="/andrejbauer/lvr-coq/commits/master/Sorting.v" class="button minibutton " rel="nofollow">History</a>
        </div><!-- /.button-group -->
          <a class="minibutton danger disabled empty-icon tooltipped tooltipped-w" href="#"
             aria-label="You must be signed in to make or propose changes">
          Delete
        </a>
      </div><!-- /.actions -->
    </div>
      
  <div class="blob-wrapper data type-coq js-blob-data">
       <table class="file-code file-diff tab-size-8">
         <tr class="file-code-line">
           <td class="blob-line-nums">
             <span id="L1" rel="#L1">1</span>
<span id="L2" rel="#L2">2</span>
<span id="L3" rel="#L3">3</span>
<span id="L4" rel="#L4">4</span>
<span id="L5" rel="#L5">5</span>
<span id="L6" rel="#L6">6</span>
<span id="L7" rel="#L7">7</span>
<span id="L8" rel="#L8">8</span>
<span id="L9" rel="#L9">9</span>
<span id="L10" rel="#L10">10</span>
<span id="L11" rel="#L11">11</span>
<span id="L12" rel="#L12">12</span>
<span id="L13" rel="#L13">13</span>
<span id="L14" rel="#L14">14</span>
<span id="L15" rel="#L15">15</span>
<span id="L16" rel="#L16">16</span>
<span id="L17" rel="#L17">17</span>
<span id="L18" rel="#L18">18</span>
<span id="L19" rel="#L19">19</span>
<span id="L20" rel="#L20">20</span>
<span id="L21" rel="#L21">21</span>
<span id="L22" rel="#L22">22</span>
<span id="L23" rel="#L23">23</span>
<span id="L24" rel="#L24">24</span>
<span id="L25" rel="#L25">25</span>
<span id="L26" rel="#L26">26</span>
<span id="L27" rel="#L27">27</span>
<span id="L28" rel="#L28">28</span>
<span id="L29" rel="#L29">29</span>
<span id="L30" rel="#L30">30</span>
<span id="L31" rel="#L31">31</span>
<span id="L32" rel="#L32">32</span>
<span id="L33" rel="#L33">33</span>
<span id="L34" rel="#L34">34</span>
<span id="L35" rel="#L35">35</span>
<span id="L36" rel="#L36">36</span>
<span id="L37" rel="#L37">37</span>
<span id="L38" rel="#L38">38</span>
<span id="L39" rel="#L39">39</span>
<span id="L40" rel="#L40">40</span>
<span id="L41" rel="#L41">41</span>
<span id="L42" rel="#L42">42</span>
<span id="L43" rel="#L43">43</span>
<span id="L44" rel="#L44">44</span>
<span id="L45" rel="#L45">45</span>
<span id="L46" rel="#L46">46</span>
<span id="L47" rel="#L47">47</span>
<span id="L48" rel="#L48">48</span>
<span id="L49" rel="#L49">49</span>
<span id="L50" rel="#L50">50</span>
<span id="L51" rel="#L51">51</span>
<span id="L52" rel="#L52">52</span>
<span id="L53" rel="#L53">53</span>
<span id="L54" rel="#L54">54</span>
<span id="L55" rel="#L55">55</span>
<span id="L56" rel="#L56">56</span>
<span id="L57" rel="#L57">57</span>
<span id="L58" rel="#L58">58</span>
<span id="L59" rel="#L59">59</span>
<span id="L60" rel="#L60">60</span>
<span id="L61" rel="#L61">61</span>
<span id="L62" rel="#L62">62</span>
<span id="L63" rel="#L63">63</span>
<span id="L64" rel="#L64">64</span>
<span id="L65" rel="#L65">65</span>
<span id="L66" rel="#L66">66</span>
<span id="L67" rel="#L67">67</span>
<span id="L68" rel="#L68">68</span>
<span id="L69" rel="#L69">69</span>
<span id="L70" rel="#L70">70</span>
<span id="L71" rel="#L71">71</span>
<span id="L72" rel="#L72">72</span>
<span id="L73" rel="#L73">73</span>
<span id="L74" rel="#L74">74</span>
<span id="L75" rel="#L75">75</span>
<span id="L76" rel="#L76">76</span>
<span id="L77" rel="#L77">77</span>
<span id="L78" rel="#L78">78</span>
<span id="L79" rel="#L79">79</span>
<span id="L80" rel="#L80">80</span>
<span id="L81" rel="#L81">81</span>
<span id="L82" rel="#L82">82</span>
<span id="L83" rel="#L83">83</span>
<span id="L84" rel="#L84">84</span>
<span id="L85" rel="#L85">85</span>
<span id="L86" rel="#L86">86</span>
<span id="L87" rel="#L87">87</span>
<span id="L88" rel="#L88">88</span>
<span id="L89" rel="#L89">89</span>
<span id="L90" rel="#L90">90</span>
<span id="L91" rel="#L91">91</span>
<span id="L92" rel="#L92">92</span>
<span id="L93" rel="#L93">93</span>
<span id="L94" rel="#L94">94</span>
<span id="L95" rel="#L95">95</span>
<span id="L96" rel="#L96">96</span>
<span id="L97" rel="#L97">97</span>
<span id="L98" rel="#L98">98</span>
<span id="L99" rel="#L99">99</span>
<span id="L100" rel="#L100">100</span>
<span id="L101" rel="#L101">101</span>
<span id="L102" rel="#L102">102</span>
<span id="L103" rel="#L103">103</span>
<span id="L104" rel="#L104">104</span>
<span id="L105" rel="#L105">105</span>
<span id="L106" rel="#L106">106</span>
<span id="L107" rel="#L107">107</span>
<span id="L108" rel="#L108">108</span>
<span id="L109" rel="#L109">109</span>
<span id="L110" rel="#L110">110</span>
<span id="L111" rel="#L111">111</span>
<span id="L112" rel="#L112">112</span>
<span id="L113" rel="#L113">113</span>
<span id="L114" rel="#L114">114</span>
<span id="L115" rel="#L115">115</span>
<span id="L116" rel="#L116">116</span>
<span id="L117" rel="#L117">117</span>
<span id="L118" rel="#L118">118</span>
<span id="L119" rel="#L119">119</span>
<span id="L120" rel="#L120">120</span>
<span id="L121" rel="#L121">121</span>
<span id="L122" rel="#L122">122</span>
<span id="L123" rel="#L123">123</span>
<span id="L124" rel="#L124">124</span>
<span id="L125" rel="#L125">125</span>
<span id="L126" rel="#L126">126</span>
<span id="L127" rel="#L127">127</span>
<span id="L128" rel="#L128">128</span>
<span id="L129" rel="#L129">129</span>
<span id="L130" rel="#L130">130</span>
<span id="L131" rel="#L131">131</span>
<span id="L132" rel="#L132">132</span>
<span id="L133" rel="#L133">133</span>
<span id="L134" rel="#L134">134</span>
<span id="L135" rel="#L135">135</span>
<span id="L136" rel="#L136">136</span>
<span id="L137" rel="#L137">137</span>
<span id="L138" rel="#L138">138</span>
<span id="L139" rel="#L139">139</span>
<span id="L140" rel="#L140">140</span>
<span id="L141" rel="#L141">141</span>
<span id="L142" rel="#L142">142</span>
<span id="L143" rel="#L143">143</span>
<span id="L144" rel="#L144">144</span>
<span id="L145" rel="#L145">145</span>
<span id="L146" rel="#L146">146</span>
<span id="L147" rel="#L147">147</span>
<span id="L148" rel="#L148">148</span>
<span id="L149" rel="#L149">149</span>
<span id="L150" rel="#L150">150</span>
<span id="L151" rel="#L151">151</span>
<span id="L152" rel="#L152">152</span>
<span id="L153" rel="#L153">153</span>
<span id="L154" rel="#L154">154</span>
<span id="L155" rel="#L155">155</span>
<span id="L156" rel="#L156">156</span>
<span id="L157" rel="#L157">157</span>
<span id="L158" rel="#L158">158</span>
<span id="L159" rel="#L159">159</span>
<span id="L160" rel="#L160">160</span>
<span id="L161" rel="#L161">161</span>
<span id="L162" rel="#L162">162</span>
<span id="L163" rel="#L163">163</span>
<span id="L164" rel="#L164">164</span>
<span id="L165" rel="#L165">165</span>
<span id="L166" rel="#L166">166</span>
<span id="L167" rel="#L167">167</span>
<span id="L168" rel="#L168">168</span>
<span id="L169" rel="#L169">169</span>
<span id="L170" rel="#L170">170</span>
<span id="L171" rel="#L171">171</span>
<span id="L172" rel="#L172">172</span>
<span id="L173" rel="#L173">173</span>
<span id="L174" rel="#L174">174</span>
<span id="L175" rel="#L175">175</span>
<span id="L176" rel="#L176">176</span>
<span id="L177" rel="#L177">177</span>
<span id="L178" rel="#L178">178</span>
<span id="L179" rel="#L179">179</span>
<span id="L180" rel="#L180">180</span>
<span id="L181" rel="#L181">181</span>
<span id="L182" rel="#L182">182</span>
<span id="L183" rel="#L183">183</span>
<span id="L184" rel="#L184">184</span>
<span id="L185" rel="#L185">185</span>
<span id="L186" rel="#L186">186</span>
<span id="L187" rel="#L187">187</span>
<span id="L188" rel="#L188">188</span>
<span id="L189" rel="#L189">189</span>
<span id="L190" rel="#L190">190</span>
<span id="L191" rel="#L191">191</span>
<span id="L192" rel="#L192">192</span>
<span id="L193" rel="#L193">193</span>
<span id="L194" rel="#L194">194</span>
<span id="L195" rel="#L195">195</span>
<span id="L196" rel="#L196">196</span>
<span id="L197" rel="#L197">197</span>
<span id="L198" rel="#L198">198</span>
<span id="L199" rel="#L199">199</span>
<span id="L200" rel="#L200">200</span>
<span id="L201" rel="#L201">201</span>
<span id="L202" rel="#L202">202</span>
<span id="L203" rel="#L203">203</span>
<span id="L204" rel="#L204">204</span>
<span id="L205" rel="#L205">205</span>
<span id="L206" rel="#L206">206</span>
<span id="L207" rel="#L207">207</span>
<span id="L208" rel="#L208">208</span>
<span id="L209" rel="#L209">209</span>
<span id="L210" rel="#L210">210</span>
<span id="L211" rel="#L211">211</span>
<span id="L212" rel="#L212">212</span>
<span id="L213" rel="#L213">213</span>
<span id="L214" rel="#L214">214</span>
<span id="L215" rel="#L215">215</span>
<span id="L216" rel="#L216">216</span>
<span id="L217" rel="#L217">217</span>
<span id="L218" rel="#L218">218</span>
<span id="L219" rel="#L219">219</span>
<span id="L220" rel="#L220">220</span>
<span id="L221" rel="#L221">221</span>
<span id="L222" rel="#L222">222</span>
<span id="L223" rel="#L223">223</span>
<span id="L224" rel="#L224">224</span>
<span id="L225" rel="#L225">225</span>
<span id="L226" rel="#L226">226</span>
<span id="L227" rel="#L227">227</span>
<span id="L228" rel="#L228">228</span>
<span id="L229" rel="#L229">229</span>
<span id="L230" rel="#L230">230</span>
<span id="L231" rel="#L231">231</span>
<span id="L232" rel="#L232">232</span>

           </td>
           <td class="blob-line-code"><div class="code-body highlight"><pre><div class='line' id='LC1'><span class="c">(** Podpora za algoritme za urejanje. *)</span></div><div class='line' id='LC2'><br/></div><div class='line' id='LC3'><span class="c">(** Delali bomo s seznami celih števil, pri čemer bomo uporabljali</span></div><div class='line' id='LC4'><span class="c">    cela števila iz knjižnice [ZArith]. To so binarna cela števila,</span></div><div class='line' id='LC5'><span class="c">    s katerimi lahko &quot;učinkovito&quot; računamo. *)</span></div><div class='line' id='LC6'><br/></div><div class='line' id='LC7'><span class="kn">Require</span> <span class="kn">Import</span> <span class="nn">List</span><span class="p">.</span></div><div class='line' id='LC8'><span class="nc">Require</span> <span class="kn">Import</span> <span class="nn">Bool</span><span class="p">.</span></div><div class='line' id='LC9'><span class="nc">Require</span> <span class="kn">Import</span> <span class="nn">ZArith</span><span class="p">.</span></div><div class='line' id='LC10'><br/></div><div class='line' id='LC11'><span class="c">(** Aktiviramo notacijo za sezname. *)</span></div><div class='line' id='LC12'><span class="kn">Local</span> <span class="kn">Open</span> <span class="kn">Scope</span> <span class="n">list_scope</span><span class="o">.</span></div><div class='line' id='LC13'><br/></div><div class='line' id='LC14'><span class="c">(** Najprej je treba definirati pojma &quot;seznam je urejen&quot; in</span></div><div class='line' id='LC15'><span class="c">    &quot;seznam [l1] je permutacija seznama [l2]&quot;. </span></div><div class='line' id='LC16'><span class="c">*)</span></div><div class='line' id='LC17'><br/></div><div class='line' id='LC18'><span class="c">(** Seznam je urejen, če je prazen, ima en element, ali je</span></div><div class='line' id='LC19'><span class="c">    oblike [x :: y :: _], kjer je [x &lt;= y] in je rep</span></div><div class='line' id='LC20'><span class="c">    [y :: _] urejen. </span></div><div class='line' id='LC21'><br/></div><div class='line' id='LC22'><span class="c">    Uporabili bomo vzorec [(y :: _) as l&#39;], ki pomeni &quot;seznam</span></div><div class='line' id='LC23'><span class="c">    [l&#39;] oblike [y :: _]&quot;. S tem hkrati dobimo prvi element</span></div><div class='line' id='LC24'><span class="c">    seznama [y] in celoten seznam [l&#39;].</span></div><div class='line' id='LC25'><span class="c">*)</span></div><div class='line' id='LC26'><span class="kn">Fixpoint</span> <span class="n">urejen</span> <span class="o">(</span><span class="n">l</span> <span class="o">:</span> <span class="kt">list</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">:=</span></div><div class='line' id='LC27'>&nbsp;&nbsp;<span class="k">match</span> <span class="n">l</span> <span class="k">with</span></div><div class='line' id='LC28'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">|</span> <span class="n">nil</span> <span class="o">=&gt;</span> <span class="nc">True</span></div><div class='line' id='LC29'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">|</span> <span class="o">_</span> <span class="o">::</span> <span class="n">nil</span> <span class="o">=&gt;</span> <span class="nc">True</span></div><div class='line' id='LC30'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">|</span> <span class="n">x</span> <span class="o">::</span> <span class="o">((</span><span class="n">y</span> <span class="o">::</span> <span class="o">_)</span> <span class="k">as</span> <span class="n">l&#39;</span><span class="o">)</span> <span class="o">=&gt;</span> <span class="o">(</span><span class="n">x</span> <span class="o">&lt;=</span> <span class="n">y</span><span class="o">)%</span><span class="nc">Z</span> <span class="o">/\</span> <span class="n">urejen</span> <span class="n">l&#39;</span></div><div class='line' id='LC31'>&nbsp;&nbsp;<span class="k">end</span><span class="o">.</span></div><div class='line' id='LC32'><br/></div><div class='line' id='LC33'><span class="c">(** Za permutacije potrebujemo funkcijo, ki prešteje, kolikokrat</span></div><div class='line' id='LC34'><span class="c">    se dano število [k] pojavi v seznamu [l]. *)</span></div><div class='line' id='LC35'><span class="kn">Fixpoint</span> <span class="n">pojavi</span> <span class="o">(</span><span class="n">x</span> <span class="o">:</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">(</span><span class="n">l</span> <span class="o">:</span> <span class="kt">list</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">:=</span></div><div class='line' id='LC36'>&nbsp;&nbsp;<span class="k">match</span> <span class="n">l</span> <span class="k">with</span></div><div class='line' id='LC37'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">|</span> <span class="n">nil</span> <span class="o">=&gt;</span> <span class="mi">0</span></div><div class='line' id='LC38'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">|</span> <span class="n">y</span> <span class="o">::</span> <span class="n">l&#39;</span> <span class="o">=&gt;</span></div><div class='line' id='LC39'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="k">if</span> <span class="nn">Z</span><span class="p">.</span><span class="n">eqb</span> <span class="n">x</span> <span class="n">y</span> <span class="k">then</span> <span class="nc">S</span> <span class="o">(</span><span class="n">pojavi</span> <span class="n">x</span> <span class="n">l&#39;</span><span class="o">)</span> <span class="k">else</span> <span class="n">pojavi</span> <span class="n">x</span> <span class="n">l&#39;</span></div><div class='line' id='LC40'>&nbsp;&nbsp;<span class="k">end</span><span class="o">.</span></div><div class='line' id='LC41'><br/></div><div class='line' id='LC42'><span class="c">(** Seznama [l1] in [l2] sta enaka, če imata isto število pojavitev</span></div><div class='line' id='LC43'><span class="c">    za vsak [x]. *)</span></div><div class='line' id='LC44'><span class="kn">Definition</span> <span class="n">permutiran</span> <span class="o">(</span><span class="n">l1</span> <span class="n">l2</span> <span class="o">:</span> <span class="kt">list</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">:=</span></div><div class='line' id='LC45'>&nbsp;&nbsp;<span class="k">forall</span> <span class="n">x</span> <span class="o">:</span> <span class="nc">Z</span><span class="o">,</span> <span class="n">pojavi</span> <span class="n">x</span> <span class="n">l1</span> <span class="o">=</span> <span class="n">pojavi</span> <span class="n">x</span> <span class="n">l2</span><span class="o">.</span></div><div class='line' id='LC46'><br/></div><div class='line' id='LC47'><span class="c">(** Uvedemo notacijo za [permutiran l1 l2]. *)</span></div><div class='line' id='LC48'><span class="kn">Notation</span> <span class="s2">&quot;l1 ~~ l2&quot;</span> <span class="o">:=</span> <span class="o">(</span><span class="n">permutiran</span> <span class="n">l1</span> <span class="n">l2</span><span class="o">)</span> <span class="o">(</span><span class="n">at</span> <span class="n">level</span> <span class="mi">70</span><span class="o">).</span></div><div class='line' id='LC49'><br/></div><div class='line' id='LC50'><span class="c">(** Relacija [permutiran] je ekvivalenčna relacija. *)</span></div><div class='line' id='LC51'><span class="kn">Lemma</span> <span class="n">permutiran_refl</span> <span class="o">(</span><span class="n">l</span> <span class="o">:</span> <span class="kt">list</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">:</span> <span class="n">l</span> <span class="o">~~</span> <span class="n">l</span><span class="o">.</span></div><div class='line' id='LC52'><span class="kn">Proof</span><span class="o">.</span></div><div class='line' id='LC53'>&nbsp;&nbsp;<span class="k">intro</span> <span class="o">;</span> <span class="kp">reflexivity</span><span class="o">.</span></div><div class='line' id='LC54'><span class="kn">Qed</span><span class="o">.</span></div><div class='line' id='LC55'><br/></div><div class='line' id='LC56'><span class="kn">Lemma</span> <span class="n">permutiran_sym</span> <span class="o">(</span><span class="n">l1</span> <span class="n">l2</span> <span class="o">:</span> <span class="kt">list</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">:</span> <span class="n">l1</span> <span class="o">~~</span> <span class="n">l2</span> <span class="o">-&gt;</span> <span class="n">l2</span> <span class="o">~~</span> <span class="n">l1</span><span class="o">.</span></div><div class='line' id='LC57'><span class="kn">Proof</span><span class="o">.</span></div><div class='line' id='LC58'>&nbsp;&nbsp;<span class="k">intros</span> <span class="nc">E</span> <span class="n">x</span><span class="o">.</span></div><div class='line' id='LC59'>&nbsp;&nbsp;<span class="k">symmetry</span><span class="o">.</span></div><div class='line' id='LC60'>&nbsp;&nbsp;<span class="k">apply</span> <span class="nn">E</span><span class="p">.</span></div><div class='line' id='LC61'><span class="nn">Qed</span><span class="p">.</span></div><div class='line' id='LC62'><br/></div><div class='line' id='LC63'><span class="nc">Lemma</span> <span class="n">permutiran_tran</span> <span class="o">(</span><span class="n">l1</span> <span class="n">l2</span> <span class="n">l3</span> <span class="o">:</span> <span class="kt">list</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">:</span> <span class="n">l1</span> <span class="o">~~</span> <span class="n">l2</span> <span class="o">-&gt;</span> <span class="n">l2</span> <span class="o">~~</span> <span class="n">l3</span> <span class="o">-&gt;</span> <span class="n">l1</span> <span class="o">~~</span> <span class="n">l3</span><span class="o">.</span></div><div class='line' id='LC64'><span class="kn">Proof</span><span class="o">.</span></div><div class='line' id='LC65'>&nbsp;&nbsp;<span class="k">intros</span> <span class="nc">E1</span> <span class="nc">E2</span> <span class="n">x</span><span class="o">.</span></div><div class='line' id='LC66'>&nbsp;&nbsp;<span class="k">transitivity</span> <span class="o">(</span><span class="n">pojavi</span> <span class="n">x</span> <span class="n">l2</span><span class="o">)</span> <span class="o">;</span> <span class="k">auto</span><span class="o">.</span></div><div class='line' id='LC67'><span class="kn">Qed</span><span class="o">.</span></div><div class='line' id='LC68'>&nbsp;&nbsp;</div><div class='line' id='LC69'><span class="c">(** Zveza med [pojavi] in stikanjem seznamov. *)</span></div><div class='line' id='LC70'><span class="kn">Lemma</span> <span class="n">pojavi_app</span> <span class="o">(</span><span class="n">x</span> <span class="o">:</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">(</span><span class="n">l1</span> <span class="n">l2</span> <span class="o">:</span> <span class="kt">list</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">:</span> <span class="n">pojavi</span> <span class="n">x</span> <span class="o">(</span><span class="n">l1</span> <span class="o">++</span> <span class="n">l2</span><span class="o">)</span> <span class="o">=</span> <span class="n">pojavi</span> <span class="n">x</span> <span class="n">l1</span> <span class="o">+</span> <span class="n">pojavi</span> <span class="n">x</span> <span class="n">l2</span><span class="o">.</span></div><div class='line' id='LC71'><span class="kn">Proof</span><span class="o">.</span></div><div class='line' id='LC72'>&nbsp;&nbsp;<span class="k">induction</span> <span class="n">l1</span> <span class="o">;</span> <span class="k">simpl</span> <span class="o">;</span> <span class="k">auto</span><span class="o">.</span></div><div class='line' id='LC73'>&nbsp;&nbsp;<span class="k">case</span> <span class="o">((</span><span class="n">x</span> <span class="o">=?</span> <span class="n">a</span><span class="o">)%</span><span class="nc">Z</span><span class="o">)</span> <span class="o">;</span> <span class="kp">omega</span><span class="o">.</span></div><div class='line' id='LC74'><span class="kn">Qed</span><span class="o">.</span></div><div class='line' id='LC75'><br/></div><div class='line' id='LC76'><span class="c">(** Potrebovali bomo tudi operacije, ki sezname razdelijo na dva</span></div><div class='line' id='LC77'><span class="c">    podseznama. Na primer, v urejanju z zlivanjem seznam razdelimo</span></div><div class='line' id='LC78'><span class="c">    takole: *)</span></div><div class='line' id='LC79'><span class="kn">Fixpoint</span> <span class="n">razpolovi</span> <span class="o">(</span><span class="n">l</span> <span class="o">:</span> <span class="kt">list</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">:=</span></div><div class='line' id='LC80'>&nbsp;&nbsp;<span class="k">match</span> <span class="n">l</span> <span class="k">with</span></div><div class='line' id='LC81'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">|</span> <span class="n">nil</span> <span class="o">=&gt;</span> <span class="o">(</span><span class="n">nil</span><span class="o">,</span> <span class="n">nil</span><span class="o">)</span></div><div class='line' id='LC82'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">|</span> <span class="n">x</span> <span class="o">::</span> <span class="n">nil</span> <span class="o">=&gt;</span> <span class="o">(</span><span class="n">nil</span><span class="o">,</span> <span class="n">x</span> <span class="o">::</span> <span class="n">nil</span><span class="o">)</span></div><div class='line' id='LC83'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">|</span> <span class="n">x</span> <span class="o">::</span> <span class="n">y</span> <span class="o">::</span> <span class="n">l&#39;</span> <span class="o">=&gt;</span></div><div class='line' id='LC84'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="k">let</span> <span class="o">(</span><span class="n">l1</span><span class="o">,</span> <span class="n">l2</span><span class="o">)</span> <span class="o">:=</span> <span class="n">razpolovi</span> <span class="n">l&#39;</span> <span class="k">in</span></div><div class='line' id='LC85'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">(</span><span class="n">x</span> <span class="o">::</span> <span class="n">l1</span><span class="o">,</span> <span class="n">y</span> <span class="o">::</span> <span class="n">l2</span><span class="o">)</span></div><div class='line' id='LC86'>&nbsp;&nbsp;<span class="k">end</span><span class="o">.</span></div><div class='line' id='LC87'><br/></div><div class='line' id='LC88'><span class="nc">Eval</span> <span class="k">compute</span> <span class="k">in</span> <span class="o">(</span><span class="n">razpolovi</span> <span class="o">(</span><span class="mi">1</span> <span class="o">::</span> <span class="mi">2</span> <span class="o">::</span> <span class="mi">3</span> <span class="o">::</span> <span class="mi">4</span> <span class="o">::</span> <span class="mi">5</span> <span class="o">::</span> <span class="mi">6</span> <span class="o">::</span> <span class="mi">7</span> <span class="o">::</span> <span class="mi">8</span> <span class="o">::</span> <span class="mi">9</span> <span class="o">::</span> <span class="n">nil</span><span class="o">)%</span><span class="nc">Z</span><span class="o">).</span></div><div class='line' id='LC89'><br/></div><div class='line' id='LC90'><span class="c">(** To je pomožna oblika indukcije na seznamih. Pravi, pa tole:</span></div><div class='line' id='LC91'><span class="c">    denimo, da lastnost P in da</span></div><div class='line' id='LC92'><br/></div><div class='line' id='LC93'><span class="c">    - nil ima lastnost P</span></div><div class='line' id='LC94'><span class="c">    - seznam z enim elementom (x :: nil) ima lastnost P, za vsak x</span></div><div class='line' id='LC95'><span class="c">    - če ima seznam l lastnost P, potem ima tudi x :: y :: l lastnost P,</span></div><div class='line' id='LC96'><span class="c">      za vse x, y, l</span></div><div class='line' id='LC97'><br/></div><div class='line' id='LC98'><span class="c">    Tedaj ima vsak seznam lasnost P.</span></div><div class='line' id='LC99'><br/></div><div class='line' id='LC100'><span class="c">    To inačico indukcije najlažje dokažemo tako, da napišemo ustrezno</span></div><div class='line' id='LC101'><span class="c">    rekurzivno funkcijo, ki je po Curry-Howardu njen dokaz.</span></div><div class='line' id='LC102'><span class="c">*)</span></div><div class='line' id='LC103'><span class="kn">Fixpoint</span> <span class="n">list_ind_2</span></div><div class='line' id='LC104'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">{</span><span class="nc">A</span> <span class="o">:</span> <span class="kn">Set</span><span class="o">}</span></div><div class='line' id='LC105'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">(</span><span class="nc">P</span> <span class="o">:</span> <span class="kt">list</span> <span class="nc">A</span> <span class="o">-&gt;</span> <span class="kt">Prop</span><span class="o">)</span></div><div class='line' id='LC106'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">(</span><span class="n">p0</span> <span class="o">:</span> <span class="nc">P</span> <span class="n">nil</span><span class="o">)</span></div><div class='line' id='LC107'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">(</span><span class="n">p1</span> <span class="o">:</span> <span class="k">forall</span> <span class="n">x</span><span class="o">,</span> <span class="nc">P</span> <span class="o">(</span><span class="n">x</span> <span class="o">::</span> <span class="n">nil</span><span class="o">))</span></div><div class='line' id='LC108'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">(</span><span class="n">p2</span> <span class="o">:</span> <span class="k">forall</span> <span class="n">a</span> <span class="n">b</span> <span class="n">k</span><span class="o">,</span> <span class="nc">P</span> <span class="n">k</span> <span class="o">-&gt;</span> <span class="nc">P</span> <span class="o">(</span><span class="n">a</span> <span class="o">::</span> <span class="n">b</span> <span class="o">::</span> <span class="n">k</span><span class="o">))</span></div><div class='line' id='LC109'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">(</span><span class="n">l</span> <span class="o">:</span> <span class="kt">list</span> <span class="nc">A</span><span class="o">)</span> <span class="o">:=</span></div><div class='line' id='LC110'>&nbsp;&nbsp;<span class="k">match</span> <span class="n">l</span> <span class="k">with</span></div><div class='line' id='LC111'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">|</span> <span class="n">nil</span> <span class="o">=&gt;</span> <span class="n">p0</span></div><div class='line' id='LC112'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">|</span> <span class="n">x</span> <span class="o">::</span> <span class="n">nil</span> <span class="o">=&gt;</span> <span class="n">p1</span> <span class="n">x</span></div><div class='line' id='LC113'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">|</span> <span class="n">x</span> <span class="o">::</span> <span class="n">y</span> <span class="o">::</span> <span class="n">l&#39;</span> <span class="o">=&gt;</span> <span class="n">p2</span> <span class="n">x</span> <span class="n">y</span> <span class="n">l&#39;</span> <span class="o">(</span><span class="n">list_ind_2</span> <span class="nc">P</span> <span class="n">p0</span> <span class="n">p1</span> <span class="n">p2</span> <span class="n">l&#39;</span><span class="o">)</span></div><div class='line' id='LC114'>&nbsp;&nbsp;<span class="k">end</span><span class="o">.</span></div><div class='line' id='LC115'><br/></div><div class='line' id='LC116'><span class="c">(** Osnovne lastnosti razpolavljanja. *)</span></div><div class='line' id='LC117'><br/></div><div class='line' id='LC118'><span class="kn">Lemma</span> <span class="n">razpolovi_length</span> <span class="o">(</span><span class="n">l</span> <span class="o">:</span> <span class="kt">list</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">:</span></div><div class='line' id='LC119'>&nbsp;&nbsp;<span class="k">match</span> <span class="n">razpolovi</span> <span class="n">l</span> <span class="k">with</span></div><div class='line' id='LC120'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">|</span> <span class="o">(</span><span class="n">l1</span><span class="o">,</span> <span class="n">l2</span><span class="o">)</span> <span class="o">=&gt;</span> <span class="n">length</span> <span class="n">l</span> <span class="o">=</span> <span class="n">length</span> <span class="n">l1</span> <span class="o">+</span> <span class="n">length</span> <span class="n">l2</span></div><div class='line' id='LC121'>&nbsp;&nbsp;<span class="k">end</span><span class="o">.</span></div><div class='line' id='LC122'><span class="kn">Proof</span><span class="o">.</span></div><div class='line' id='LC123'>&nbsp;&nbsp;<span class="k">apply</span> <span class="o">(</span><span class="n">list_ind_2</span> <span class="o">(</span><span class="k">fun</span> <span class="n">l</span> <span class="o">=&gt;</span></div><div class='line' id='LC124'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="k">let</span> <span class="o">(</span><span class="n">l1</span><span class="o">,</span> <span class="n">l2</span><span class="o">)</span> <span class="o">:=</span> <span class="n">razpolovi</span> <span class="n">l</span> <span class="k">in</span></div><div class='line' id='LC125'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="n">length</span> <span class="n">l</span> <span class="o">=</span> <span class="n">length</span> <span class="n">l1</span> <span class="o">+</span> <span class="n">length</span> <span class="n">l2</span><span class="o">))</span> <span class="o">;</span></div><div class='line' id='LC126'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="k">simpl</span> <span class="o">;</span> <span class="k">auto</span><span class="o">.</span></div><div class='line' id='LC127'>&nbsp;&nbsp;<span class="k">intros</span> <span class="n">x</span> <span class="n">y</span> <span class="n">l&#39;</span> <span class="nn">H</span><span class="p">.</span></div><div class='line' id='LC128'>&nbsp;&nbsp;<span class="n">replace</span> <span class="o">(</span><span class="n">razpolovi</span> <span class="n">l&#39;</span><span class="o">)</span> <span class="k">with</span> <span class="o">(</span><span class="n">fst</span> <span class="o">(</span><span class="n">razpolovi</span> <span class="n">l&#39;</span><span class="o">),</span> <span class="n">snd</span> <span class="o">(</span><span class="n">razpolovi</span> <span class="n">l&#39;</span><span class="o">))</span> <span class="k">in</span> <span class="o">*</span> <span class="o">|-</span> <span class="o">*</span> <span class="o">;</span></div><div class='line' id='LC129'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">[</span> <span class="kr">idtac</span> <span class="o">|</span> <span class="k">symmetry</span> <span class="o">;</span> <span class="k">apply</span> <span class="n">surjective_pairing</span> <span class="o">].</span></div><div class='line' id='LC130'>&nbsp;&nbsp;<span class="k">simpl</span><span class="o">.</span></div><div class='line' id='LC131'>&nbsp;&nbsp;<span class="nc">SearchAbout</span> <span class="o">(?</span><span class="n">x</span> <span class="o">+</span> <span class="nc">S</span> <span class="o">?</span><span class="n">y</span><span class="o">).</span></div><div class='line' id='LC132'>&nbsp;&nbsp;<span class="k">rewrite</span> <span class="o">&lt;-</span> <span class="n">plus_n_Sm</span><span class="o">.</span></div><div class='line' id='LC133'>&nbsp;&nbsp;<span class="n">now</span> <span class="kr">repeat</span> <span class="n">f_equal</span><span class="o">.</span></div><div class='line' id='LC134'><span class="kn">Qed</span><span class="o">.</span></div><div class='line' id='LC135'><br/></div><div class='line' id='LC136'><span class="c">(** Nekateri algoritmi za urejanje razdelijo seznam na podseznama</span></div><div class='line' id='LC137'><span class="c">    glede na dani kriterij [p]. *)</span></div><div class='line' id='LC138'><span class="kn">Fixpoint</span> <span class="n">razdeli</span> <span class="o">(</span><span class="n">p</span> <span class="o">:</span> <span class="nc">Z</span> <span class="o">-&gt;</span> <span class="kt">bool</span><span class="o">)</span> <span class="o">(</span><span class="n">l</span> <span class="o">:</span> <span class="kt">list</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">:=</span></div><div class='line' id='LC139'>&nbsp;&nbsp;<span class="k">match</span> <span class="n">l</span> <span class="k">with</span></div><div class='line' id='LC140'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">|</span> <span class="n">nil</span> <span class="o">=&gt;</span> <span class="o">(</span><span class="n">nil</span><span class="o">,</span> <span class="n">nil</span><span class="o">)</span></div><div class='line' id='LC141'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">|</span> <span class="n">x</span> <span class="o">::</span> <span class="n">l&#39;</span> <span class="o">=&gt;</span></div><div class='line' id='LC142'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="k">let</span> <span class="o">(</span><span class="n">l1</span><span class="o">,</span> <span class="n">l2</span><span class="o">)</span> <span class="o">:=</span> <span class="n">razdeli</span> <span class="n">p</span> <span class="n">l&#39;</span> <span class="k">in</span></div><div class='line' id='LC143'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="k">if</span> <span class="n">p</span> <span class="n">x</span> <span class="k">then</span> <span class="o">(</span><span class="n">x</span> <span class="o">::</span> <span class="n">l1</span><span class="o">,</span> <span class="n">l2</span><span class="o">)</span> <span class="k">else</span> <span class="o">(</span><span class="n">l1</span><span class="o">,</span> <span class="n">x</span> <span class="o">::</span> <span class="n">l2</span><span class="o">)</span></div><div class='line' id='LC144'>&nbsp;&nbsp;<span class="k">end</span><span class="o">.</span></div><div class='line' id='LC145'><br/></div><div class='line' id='LC146'><span class="c">(** Na primer, takole razdelimo dani seznam glede na to,</span></div><div class='line' id='LC147'><span class="c">    ali so elementi večji od 5. *)</span></div><div class='line' id='LC148'><span class="nc">Eval</span> <span class="k">compute</span> <span class="k">in</span> <span class="o">(</span><span class="n">razdeli</span> <span class="o">(</span><span class="nn">Z</span><span class="p">.</span><span class="n">leb</span> <span class="mi">5</span><span class="o">)</span> <span class="o">(</span><span class="mi">10</span> <span class="o">::</span> <span class="mi">1</span> <span class="o">::</span> <span class="mi">1</span> <span class="o">::</span> <span class="mi">3</span> <span class="o">::</span> <span class="mi">8</span> <span class="o">::</span> <span class="mi">7</span> <span class="o">::</span> <span class="mi">5</span> <span class="o">::</span> <span class="n">nil</span><span class="o">)%</span><span class="nc">Z</span><span class="o">).</span></div><div class='line' id='LC149'>&nbsp;</div><div class='line' id='LC150'><span class="kn">Lemma</span> <span class="n">razdeli_length</span> <span class="o">(</span><span class="n">p</span> <span class="o">:</span> <span class="nc">Z</span> <span class="o">-&gt;</span> <span class="kt">bool</span><span class="o">)</span> <span class="o">(</span><span class="n">l</span> <span class="o">:</span> <span class="kt">list</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">:</span></div><div class='line' id='LC151'>&nbsp;&nbsp;<span class="k">let</span> <span class="o">(</span><span class="n">l1</span><span class="o">,</span> <span class="n">l2</span><span class="o">)</span> <span class="o">:=</span> <span class="n">razdeli</span> <span class="n">p</span> <span class="n">l</span> <span class="k">in</span></div><div class='line' id='LC152'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="n">length</span> <span class="n">l</span> <span class="o">=</span> <span class="n">length</span> <span class="n">l1</span> <span class="o">+</span> <span class="n">length</span> <span class="n">l2</span><span class="o">.</span></div><div class='line' id='LC153'><span class="kn">Proof</span><span class="o">.</span></div><div class='line' id='LC154'>&nbsp;&nbsp;<span class="k">induction</span> <span class="n">l</span><span class="o">.</span></div><div class='line' id='LC155'>&nbsp;&nbsp;<span class="o">-</span> <span class="k">simpl</span> <span class="o">;</span> <span class="k">auto</span><span class="o">.</span></div><div class='line' id='LC156'>&nbsp;&nbsp;<span class="o">-</span> <span class="k">simpl</span><span class="o">.</span></div><div class='line' id='LC157'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="k">replace</span> <span class="o">(</span><span class="n">razdeli</span> <span class="n">p</span> <span class="n">l</span><span class="o">)</span> <span class="k">with</span> <span class="o">(</span><span class="n">fst</span> <span class="o">(</span><span class="n">razdeli</span> <span class="n">p</span> <span class="n">l</span><span class="o">),</span> <span class="n">snd</span> <span class="o">(</span><span class="n">razdeli</span> <span class="n">p</span> <span class="n">l</span><span class="o">))</span> <span class="k">in</span> <span class="o">*</span> <span class="o">|-</span> <span class="o">*</span> <span class="o">;</span></div><div class='line' id='LC158'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">[</span> <span class="kr">idtac</span> <span class="o">|</span> <span class="k">symmetry</span> <span class="o">;</span> <span class="k">apply</span> <span class="n">surjective_pairing</span> <span class="o">].</span></div><div class='line' id='LC159'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="k">destruct</span> <span class="o">(</span><span class="n">p</span> <span class="n">a</span><span class="o">)</span> <span class="o">;</span> <span class="k">simpl</span><span class="o">.</span></div><div class='line' id='LC160'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">+</span> <span class="n">now</span> <span class="n">f_equal</span><span class="o">.</span></div><div class='line' id='LC161'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">+</span> <span class="k">rewrite</span> <span class="o">&lt;-</span> <span class="n">plus_n_Sm</span><span class="o">.</span></div><div class='line' id='LC162'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="n">now</span> <span class="n">f_equal</span><span class="o">.</span></div><div class='line' id='LC163'><span class="kn">Qed</span><span class="o">.</span></div><div class='line' id='LC164'><br/></div><div class='line' id='LC165'><span class="c">(** Nekateri algoritmi izračunajo minimalni element seznama. </span></div><div class='line' id='LC166'><span class="c">    Ker minimalni element praznega seznama ne obstaja, vedno</span></div><div class='line' id='LC167'><span class="c">    računamo minimalni element sestavljenega seznama [x :: l].</span></div><div class='line' id='LC168'><span class="c">*)</span></div><div class='line' id='LC169'><span class="kn">Fixpoint</span> <span class="n">najmanjsi</span> <span class="o">(</span><span class="n">x</span> <span class="o">:</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">(</span><span class="n">l</span> <span class="o">:</span> <span class="kt">list</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">:</span> <span class="nc">Z</span> <span class="o">:=</span></div><div class='line' id='LC170'>&nbsp;&nbsp;<span class="k">match</span> <span class="n">l</span> <span class="k">with</span></div><div class='line' id='LC171'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">|</span> <span class="n">nil</span> <span class="o">=&gt;</span> <span class="n">x</span></div><div class='line' id='LC172'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">|</span> <span class="n">y</span> <span class="o">::</span> <span class="n">l&#39;</span> <span class="o">=&gt;</span></div><div class='line' id='LC173'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="k">match</span> <span class="nn">Z</span><span class="p">.</span><span class="n">leb</span> <span class="n">x</span> <span class="n">y</span> <span class="k">with</span></div><div class='line' id='LC174'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">|</span> <span class="bp">true</span> <span class="o">=&gt;</span> <span class="n">najmanjsi</span> <span class="n">x</span> <span class="n">l&#39;</span></div><div class='line' id='LC175'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">|</span> <span class="bp">false</span> <span class="o">=&gt;</span> <span class="n">najmanjsi</span> <span class="n">y</span> <span class="n">l&#39;</span></div><div class='line' id='LC176'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="k">end</span></div><div class='line' id='LC177'>&nbsp;&nbsp;<span class="k">end</span><span class="o">.</span></div><div class='line' id='LC178'><br/></div><div class='line' id='LC179'><span class="nc">Eval</span> <span class="k">compute</span> <span class="k">in</span> <span class="o">(</span><span class="n">najmanjsi</span> <span class="mi">4</span> <span class="o">(</span><span class="mi">10</span> <span class="o">::</span> <span class="mi">1</span> <span class="o">::</span> <span class="mi">1</span> <span class="o">::</span> <span class="mi">3</span> <span class="o">::</span> <span class="mi">8</span> <span class="o">::</span> <span class="mi">7</span> <span class="o">::</span> <span class="mi">5</span> <span class="o">::</span> <span class="n">nil</span><span class="o">)%</span><span class="nc">Z</span><span class="o">).</span></div><div class='line' id='LC180'><br/></div><div class='line' id='LC181'><span class="c">(** Tako povemo, da želimo pripadajoči program v OCamlu. *)</span></div><div class='line' id='LC182'><span class="nc">Recursive</span> <span class="nc">Extraction</span> <span class="n">najmanjsi</span><span class="o">.</span></div><div class='line' id='LC183'><br/></div><div class='line' id='LC184'><span class="c">(** Osnovne lemen o najmanjsinih elementih. *)</span></div><div class='line' id='LC185'><br/></div><div class='line' id='LC186'><span class="kn">Lemma</span> <span class="n">najmanjsi_inv</span> <span class="o">(</span><span class="n">x</span> <span class="o">:</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">(</span><span class="n">l</span> <span class="o">:</span> <span class="kt">list</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">:</span></div><div class='line' id='LC187'>&nbsp;&nbsp;<span class="n">x</span> <span class="o">=</span> <span class="n">najmanjsi</span> <span class="n">x</span> <span class="n">l</span> <span class="o">\/</span> <span class="nc">In</span> <span class="o">(</span><span class="n">najmanjsi</span> <span class="n">x</span> <span class="n">l</span><span class="o">)</span> <span class="n">l</span><span class="o">.</span></div><div class='line' id='LC188'><span class="kn">Proof</span><span class="o">.</span></div><div class='line' id='LC189'>&nbsp;&nbsp;<span class="k">generalize</span> <span class="n">x</span><span class="o">.</span></div><div class='line' id='LC190'>&nbsp;&nbsp;<span class="k">induction</span> <span class="n">l</span> <span class="o">;</span> <span class="k">auto</span><span class="o">.</span></div><div class='line' id='LC191'>&nbsp;&nbsp;<span class="k">intro</span> <span class="n">y</span><span class="o">.</span></div><div class='line' id='LC192'>&nbsp;&nbsp;<span class="k">simpl</span><span class="o">;</span> <span class="k">destruct</span> <span class="o">(</span><span class="nn">Z</span><span class="p">.</span><span class="n">leb</span> <span class="n">y</span> <span class="n">a</span><span class="o">).</span></div><div class='line' id='LC193'>&nbsp;&nbsp;<span class="o">-</span> <span class="k">destruct</span> <span class="o">(</span><span class="nc">IHl</span> <span class="n">y</span><span class="o">)</span> <span class="o">;</span> <span class="k">auto</span><span class="o">.</span></div><div class='line' id='LC194'>&nbsp;&nbsp;<span class="o">-</span> <span class="k">destruct</span> <span class="o">(</span><span class="nc">IHl</span> <span class="n">a</span><span class="o">)</span> <span class="o">;</span> <span class="k">auto</span><span class="o">.</span></div><div class='line' id='LC195'><span class="kn">Qed</span><span class="o">.</span> </div><div class='line' id='LC196'><br/></div><div class='line' id='LC197'><span class="kn">Lemma</span> <span class="n">najmanjsi_In</span> <span class="o">(</span><span class="n">x</span> <span class="o">:</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">(</span><span class="n">l</span> <span class="o">:</span> <span class="kt">list</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">:</span> </div><div class='line' id='LC198'>&nbsp;&nbsp;<span class="nc">In</span> <span class="o">(</span><span class="n">najmanjsi</span> <span class="n">x</span> <span class="n">l</span><span class="o">)</span> <span class="o">(</span><span class="n">x</span> <span class="o">::</span> <span class="n">l</span><span class="o">).</span></div><div class='line' id='LC199'><span class="kn">Proof</span><span class="o">.</span></div><div class='line' id='LC200'>&nbsp;&nbsp;<span class="k">destruct</span> <span class="o">(</span><span class="n">najmanjsi_inv</span> <span class="n">x</span> <span class="n">l</span><span class="o">).</span></div><div class='line' id='LC201'>&nbsp;&nbsp;<span class="o">-</span> <span class="k">rewrite</span> <span class="o">&lt;-</span> <span class="nc">H</span> <span class="o">;</span> <span class="k">simpl</span> <span class="o">;</span> <span class="k">auto</span><span class="o">.</span></div><div class='line' id='LC202'>&nbsp;&nbsp;<span class="o">-</span> <span class="k">simpl</span> <span class="o">;</span> <span class="k">auto</span><span class="o">.</span></div><div class='line' id='LC203'><span class="kn">Qed</span><span class="o">.</span></div><div class='line' id='LC204'><br/></div><div class='line' id='LC205'><span class="kn">Lemma</span> <span class="n">najmanjsi_head</span> <span class="o">(</span><span class="n">x</span> <span class="o">:</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">(</span><span class="n">l</span> <span class="o">:</span> <span class="kt">list</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">:</span></div><div class='line' id='LC206'>&nbsp;&nbsp;<span class="o">(</span><span class="n">najmanjsi</span> <span class="n">x</span> <span class="n">l</span> <span class="o">&lt;=</span> <span class="n">x</span><span class="o">)%</span><span class="nn">Z</span><span class="p">.</span></div><div class='line' id='LC207'><span class="nn">Proof</span><span class="p">.</span></div><div class='line' id='LC208'>&nbsp;&nbsp;<span class="n">generalize</span> <span class="n">x</span><span class="o">.</span></div><div class='line' id='LC209'>&nbsp;&nbsp;<span class="k">induction</span> <span class="n">l</span><span class="o">.</span></div><div class='line' id='LC210'>&nbsp;&nbsp;<span class="o">-</span> <span class="k">intro</span> <span class="o">;</span> <span class="kp">reflexivity</span><span class="o">.</span></div><div class='line' id='LC211'>&nbsp;&nbsp;<span class="o">-</span> <span class="k">intro</span> <span class="n">y</span> <span class="o">;</span> <span class="k">simpl</span><span class="o">.</span></div><div class='line' id='LC212'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="n">case_eq</span> <span class="o">(</span><span class="nn">Z</span><span class="p">.</span><span class="n">leb</span> <span class="n">y</span> <span class="n">a</span><span class="o">)</span> <span class="o">;</span> <span class="k">intro</span> <span class="nn">E</span><span class="p">.</span></div><div class='line' id='LC213'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">+</span> <span class="k">apply</span> <span class="nn">IHl</span><span class="p">.</span></div><div class='line' id='LC214'>&nbsp;&nbsp;&nbsp;&nbsp;<span class="o">+</span> <span class="k">transitivity</span> <span class="n">a</span> <span class="o">;</span> <span class="o">[</span><span class="k">apply</span> <span class="nc">IHl</span> <span class="o">|</span> <span class="kr">idtac</span><span class="o">].</span></div><div class='line' id='LC215'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;<span class="n">admit</span><span class="o">.</span></div><div class='line' id='LC216'><span class="kn">Qed</span><span class="o">.</span></div><div class='line' id='LC217'><br/></div><div class='line' id='LC218'><span class="kn">Lemma</span> <span class="n">najmanjsi_tail</span> <span class="n">x</span> <span class="n">y</span> <span class="n">l</span> <span class="o">:</span> <span class="nc">In</span> <span class="n">y</span> <span class="n">l</span> <span class="o">-&gt;</span> <span class="o">(</span><span class="n">najmanjsi</span> <span class="n">x</span> <span class="n">l</span> <span class="o">&lt;=</span> <span class="n">y</span><span class="o">)%</span><span class="nn">Z</span><span class="p">.</span></div><div class='line' id='LC219'><span class="nn">Proof</span><span class="p">.</span></div><div class='line' id='LC220'>&nbsp;&nbsp;<span class="n">generalize</span> <span class="n">x</span> <span class="n">y</span> <span class="o">;</span> <span class="k">clear</span> <span class="n">x</span> <span class="n">y</span><span class="o">.</span></div><div class='line' id='LC221'>&nbsp;&nbsp;<span class="k">induction</span> <span class="n">l</span> <span class="o">;</span> <span class="o">[</span><span class="k">intros</span> <span class="o">?</span> <span class="o">?</span> <span class="nc">H</span> <span class="o">;</span> <span class="k">destruct</span> <span class="nc">H</span> <span class="o">|</span> <span class="kr">idtac</span><span class="o">].</span></div><div class='line' id='LC222'>&nbsp;&nbsp;<span class="k">intros</span> <span class="n">x</span> <span class="n">y</span> <span class="nn">H</span><span class="p">.</span></div><div class='line' id='LC223'>&nbsp;&nbsp;<span class="n">apply</span> <span class="n">in_inv</span> <span class="k">in</span> <span class="nc">H</span> <span class="o">;</span> <span class="k">destruct</span> <span class="nc">H</span> <span class="k">as</span> <span class="o">[</span><span class="nc">G</span><span class="o">|</span><span class="nc">G</span><span class="o">]</span> <span class="o">;</span> <span class="n">admit</span><span class="o">.</span></div><div class='line' id='LC224'><span class="kn">Qed</span><span class="o">.</span></div><div class='line' id='LC225'><br/></div><div class='line' id='LC226'><span class="kn">Lemma</span> <span class="n">najmanjsi_spodna_meja</span> <span class="o">(</span><span class="n">x</span> <span class="o">:</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">(</span><span class="n">l</span> <span class="o">:</span> <span class="kt">list</span> <span class="nc">Z</span><span class="o">)</span> <span class="o">:</span></div><div class='line' id='LC227'>&nbsp;&nbsp;<span class="k">forall</span> <span class="n">y</span><span class="o">,</span> <span class="nc">In</span> <span class="n">y</span> <span class="o">(</span><span class="n">x</span> <span class="o">::</span> <span class="n">l</span><span class="o">)</span> <span class="o">-&gt;</span> <span class="o">(</span><span class="n">najmanjsi</span> <span class="n">x</span> <span class="n">l</span> <span class="o">&lt;=</span> <span class="n">y</span><span class="o">)%</span><span class="nn">Z</span><span class="p">.</span></div><div class='line' id='LC228'><span class="nn">Proof</span><span class="p">.</span></div><div class='line' id='LC229'>&nbsp;&nbsp;<span class="n">intros</span> <span class="n">y</span> <span class="o">[</span><span class="nc">H</span><span class="o">|</span><span class="nc">H</span><span class="o">].</span></div><div class='line' id='LC230'>&nbsp;&nbsp;<span class="o">-</span> <span class="k">rewrite</span> <span class="nc">H</span> <span class="o">;</span> <span class="k">apply</span> <span class="n">najmanjsi_head</span><span class="o">.</span></div><div class='line' id='LC231'>&nbsp;&nbsp;<span class="o">-</span> <span class="n">now</span> <span class="k">apply</span> <span class="n">najmanjsi_tail</span><span class="o">.</span></div><div class='line' id='LC232'><span class="kn">Qed</span><span class="o">.</span> </div></pre></div></td>
         </tr>
       </table>
  </div>

  </div>
</div>

<a href="#jump-to-line" rel="facebox[.linejump]" data-hotkey="l" class="js-jump-to-line" style="display:none">Jump to Line</a>
<div id="jump-to-line" style="display:none">
  <form accept-charset="UTF-8" class="js-jump-to-line-form">
    <input class="linejump-input js-jump-to-line-field" type="text" placeholder="Jump to line&hellip;" autofocus>
    <button type="submit" class="button">Go</button>
  </form>
</div>

        </div>

      </div><!-- /.repo-container -->
      <div class="modal-backdrop"></div>
    </div><!-- /.container -->
  </div><!-- /.site -->


    </div><!-- /.wrapper -->

      <div class="container">
  <div class="site-footer">
    <ul class="site-footer-links right">
      <li><a href="https://status.github.com/">Status</a></li>
      <li><a href="http://developer.github.com">API</a></li>
      <li><a href="http://training.github.com">Training</a></li>
      <li><a href="http://shop.github.com">Shop</a></li>
      <li><a href="/blog">Blog</a></li>
      <li><a href="/about">About</a></li>

    </ul>

    <a href="/">
      <span class="mega-octicon octicon-mark-github" title="GitHub"></span>
    </a>

    <ul class="site-footer-links">
      <li>&copy; 2014 <span title="0.03096s from github-fe127-cp1-prd.iad.github.net">GitHub</span>, Inc.</li>
        <li><a href="/site/terms">Terms</a></li>
        <li><a href="/site/privacy">Privacy</a></li>
        <li><a href="/security">Security</a></li>
        <li><a href="/contact">Contact</a></li>
    </ul>
  </div><!-- /.site-footer -->
</div><!-- /.container -->


    <div class="fullscreen-overlay js-fullscreen-overlay" id="fullscreen_overlay">
  <div class="fullscreen-container js-fullscreen-container">
    <div class="textarea-wrap">
      <textarea name="fullscreen-contents" id="fullscreen-contents" class="fullscreen-contents js-fullscreen-contents" placeholder="" data-suggester="fullscreen_suggester"></textarea>
    </div>
  </div>
  <div class="fullscreen-sidebar">
    <a href="#" class="exit-fullscreen js-exit-fullscreen tooltipped tooltipped-w" aria-label="Exit Zen Mode">
      <span class="mega-octicon octicon-screen-normal"></span>
    </a>
    <a href="#" class="theme-switcher js-theme-switcher tooltipped tooltipped-w"
      aria-label="Switch themes">
      <span class="octicon octicon-color-mode"></span>
    </a>
  </div>
</div>



    <div id="ajax-error-message" class="flash flash-error">
      <span class="octicon octicon-alert"></span>
      <a href="#" class="octicon octicon-x close js-ajax-error-dismiss"></a>
      Something went wrong with that request. Please try again.
    </div>


      <script crossorigin="anonymous" src="https://assets-cdn.github.com/assets/frameworks-abd42a425136c7b864dcc59154d5f87c9aae54e3.js" type="text/javascript"></script>
      <script async="async" crossorigin="anonymous" src="https://assets-cdn.github.com/assets/github-89f79637947f64400e73b3edac016795009a2ed4.js" type="text/javascript"></script>
      
      
        <script async src="https://www.google-analytics.com/analytics.js"></script>
  </body>
</html>

