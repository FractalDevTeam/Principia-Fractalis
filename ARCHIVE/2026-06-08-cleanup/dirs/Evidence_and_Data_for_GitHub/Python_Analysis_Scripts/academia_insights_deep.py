#!/usr/bin/env python3
"""
Academia.edu DEEP INSIGHTS Analysis
Author: Pablo Cohen
Date: 2025-10-24

Purpose: Extract actionable strategic insights from Academia.edu data
- Temporal pattern discovery (day of week, time of day, seasonal)
- Visitor journey analysis (behavior patterns, session depth)
- Content performance clustering
- Strategic opportunity identification
- Competitive positioning analysis
- Growth bottleneck identification

This goes BEYOND descriptive statistics to provide ACTIONABLE intelligence
"""

import pandas as pd
import numpy as np
from datetime import datetime, timedelta
from collections import Counter, defaultdict
import json
from scipy import stats
from urllib.parse import urlparse, unquote
import warnings
warnings.filterwarnings('ignore')


class DeepInsightsAnalyzer:
    """
    Strategic insights engine for Academia.edu data
    """

    def __init__(self, csv_path):
        self.csv_path = csv_path
        self.df = None
        self.insights = []
        self.opportunities = []
        self.risks = []
        self.load_and_prepare()

    def load_and_prepare(self):
        """Load and enrich data with additional features"""
        print("="*80)
        print("DEEP INSIGHTS ANALYZER - Loading Data")
        print("="*80)

        self.df = pd.read_csv(self.csv_path, encoding='utf-8')
        self.df['Time'] = pd.to_datetime(self.df['Time'], errors='coerce')
        self.df = self.df.dropna(subset=['Time'])
        self.df = self.df.sort_values('Time')

        # Rich temporal features
        self.df['Date'] = self.df['Time'].dt.date
        self.df['Hour'] = self.df['Time'].dt.hour
        self.df['DayOfWeek'] = self.df['Time'].dt.dayofweek  # 0=Monday
        self.df['DayName'] = self.df['Time'].dt.day_name()
        self.df['WeekOfYear'] = self.df['Time'].dt.isocalendar().week
        self.df['Month'] = self.df['Time'].dt.month
        self.df['MonthName'] = self.df['Time'].dt.month_name()
        self.df['IsWeekend'] = self.df['DayOfWeek'].isin([5, 6])

        # Extract paper info
        self.df['Paper'] = self.df['URL'].apply(self.extract_paper_title)
        self.df['IsProfileView'] = self.df['Paper'] == 'Profile View'

        # Traffic source categorization
        self.df['Source'] = self.df['Referer'].apply(self.categorize_source)
        self.df['SourceCategory'] = self.df['Source'].apply(self.source_category)

        # Geographic enrichment
        self.df['IsUS'] = self.df['Country'] == 'the United States'
        self.df['Continent'] = self.df['Country'].apply(self.get_continent)

        print(f"✓ Loaded {len(self.df):,} records with enriched features")
        print(f"✓ Date range: {self.df['Time'].min().date()} to {self.df['Time'].max().date()}")

    def extract_paper_title(self, url):
        """Extract paper title from URL"""
        if pd.isna(url):
            return "Unknown"
        if 'PabloCohen' in url and url.endswith('PabloCohen'):
            return "Profile View"
        try:
            path = urlparse(url).path
            if '/academia.edu/' in url and path.count('/') >= 2:
                parts = path.split('/')
                if len(parts) > 2 and parts[1].isdigit():
                    title = unquote(parts[2]).replace('_', ' ')
                    if len(title) > 80:
                        title = title[:77] + "..."
                    return title
        except:
            pass
        return "Other Page"

    def categorize_source(self, referer):
        """Categorize traffic source"""
        if pd.isna(referer) or referer == '':
            return 'Direct/Unknown'
        try:
            domain = urlparse(referer).netloc.lower()
            if 'google' in domain:
                return 'Google'
            elif 'academia.edu' in domain:
                return 'Academia Internal'
            elif 'facebook' in domain:
                return 'Facebook'
            elif 'linkedin' in domain:
                return 'LinkedIn'
            elif 't.co' in domain or 'twitter' in domain:
                return 'Twitter'
            elif domain:
                return domain
        except:
            pass
        return 'Other'

    def source_category(self, source):
        """Categorize source into broader categories"""
        if source == 'Direct/Unknown':
            return 'Direct'
        elif source in ['Google', 'Bing', 'Yahoo', 'DuckDuckGo']:
            return 'Search'
        elif source in ['Facebook', 'Twitter', 'LinkedIn']:
            return 'Social'
        elif source == 'Academia Internal':
            return 'Internal'
        else:
            return 'Referral'

    def get_continent(self, country):
        """Map country to continent (simplified)"""
        europe = ['the United Kingdom', 'Ireland', 'Germany', 'Spain', 'France', 'Italy',
                  'the Netherlands', 'Sweden', 'Poland', 'Portugal', 'Belgium', 'Switzerland',
                  'Austria', 'Denmark', 'Norway', 'Finland', 'Greece', 'Czech Republic']
        asia = ['India', 'China', 'Japan', 'South Korea', 'Singapore', 'Thailand', 'Indonesia',
                'Philippines', 'Malaysia', 'Vietnam', 'Pakistan', 'Bangladesh', 'Israel', 'Turkey']
        americas = ['the United States', 'Canada', 'Mexico', 'Brazil', 'Argentina', 'Chile',
                    'Colombia', 'Peru', 'Venezuela']
        oceania = ['Australia', 'New Zealand']
        africa = ['South Africa', 'Nigeria', 'Kenya', 'Egypt', 'Morocco']

        if country in europe:
            return 'Europe'
        elif country in asia:
            return 'Asia'
        elif country in americas:
            return 'Americas'
        elif country in oceania:
            return 'Oceania'
        elif country in africa:
            return 'Africa'
        else:
            return 'Other'

    def analyze_temporal_patterns(self):
        """Deep temporal pattern analysis"""
        print("\n" + "="*80)
        print("INSIGHT 1: TEMPORAL PATTERNS - When Are People Reading Your Work?")
        print("="*80)

        # Day of week analysis
        dow_visitors = self.df.groupby('DayName')['Visitor ID'].nunique()
        dow_order = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday', 'Sunday']
        dow_visitors = dow_visitors.reindex(dow_order)

        # Weekend vs weekday
        weekend_visitors = self.df[self.df['IsWeekend']]['Visitor ID'].nunique()
        weekday_visitors = self.df[~self.df['IsWeekend']]['Visitor ID'].nunique()
        weekend_views = len(self.df[self.df['IsWeekend']])
        weekday_views = len(self.df[~self.df['IsWeekend']])

        # Hour of day analysis
        hour_views = self.df.groupby('Hour').size()
        peak_hour = hour_views.idxmax()
        peak_hour_views = hour_views.max()

        # Time zone interpretation (assuming UTC timestamps)
        print(f"\n📅 DAY OF WEEK PATTERNS:")
        print(f"   Weekday Visitors: {weekday_visitors} ({weekday_views} views)")
        print(f"   Weekend Visitors: {weekend_visitors} ({weekend_views} views)")

        weekend_ratio = weekend_visitors / (weekend_visitors + weekday_visitors)
        if weekend_ratio > 0.35:
            self.insights.append("⚠️ HIGH WEEKEND TRAFFIC: Your audience reads during personal time, not work hours")
            print(f"\n   🔍 INSIGHT: {weekend_ratio:.1%} of visitors come on weekends")
            print(f"      → Your work appeals to passionate individuals, not just professional researchers")
            print(f"      → Consider this is 'leisure learning' - optimize for engagement over formality")
        else:
            self.insights.append("✓ PROFESSIONAL READERSHIP: Primarily weekday traffic indicates academic/professional audience")
            print(f"\n   🔍 INSIGHT: {(1-weekend_ratio):.1%} of visitors come on weekdays")
            print(f"      → Professional/academic audience consuming during work hours")

        # Best days
        best_day = dow_visitors.idxmax()
        worst_day = dow_visitors.idxmin()
        print(f"\n   Best Day: {best_day} ({dow_visitors[best_day]} visitors)")
        print(f"   Worst Day: {worst_day} ({dow_visitors[worst_day]} visitors)")

        # Hour analysis
        print(f"\n⏰ TIME OF DAY PATTERNS:")
        print(f"   Peak Hour: {peak_hour}:00 UTC ({peak_hour_views} views)")

        # Categorize hours
        morning = hour_views[6:12].sum()    # 6am-12pm
        afternoon = hour_views[12:18].sum() # 12pm-6pm
        evening = hour_views[18:24].sum()   # 6pm-12am
        night = hour_views[0:6].sum()       # 12am-6am

        print(f"\n   Morning (6am-12pm UTC): {morning} views")
        print(f"   Afternoon (12pm-6pm UTC): {afternoon} views")
        print(f"   Evening (6pm-12am UTC): {evening} views")
        print(f"   Night (12am-6am UTC): {night} views")

        # Peak period insight
        if evening > afternoon and evening > morning:
            self.insights.append("🌙 EVENING READERS: Peak traffic in evening hours (US timezone afternoon/evening)")
            print(f"\n   🔍 INSIGHT: Evening peak suggests US-based readers consuming after work")
            self.opportunities.append("POST NEW CONTENT: Publish 12pm-3pm UTC (morning US) for maximum same-day visibility")

        # Monthly trends
        monthly_visitors = self.df.groupby('MonthName')['Visitor ID'].nunique()
        if len(monthly_visitors) > 1:
            print(f"\n📆 MONTHLY TRENDS:")
            for month in monthly_visitors.index:
                print(f"   {month}: {monthly_visitors[month]} visitors")

        return self.insights

    def analyze_visitor_behavior(self):
        """Analyze visitor journey and behavior patterns"""
        print("\n" + "="*80)
        print("INSIGHT 2: VISITOR BEHAVIOR - How Do People Engage With Your Work?")
        print("="*80)

        # Session depth analysis
        visitor_sessions = self.df.groupby('Visitor ID').agg({
            'Time': ['min', 'max', 'count'],
            'Paper': lambda x: x.nunique(),
            'URL': 'count'
        })

        visitor_sessions.columns = ['first_visit', 'last_visit', 'total_views', 'unique_papers', 'total_urls']
        visitor_sessions['session_duration'] = (visitor_sessions['last_visit'] - visitor_sessions['first_visit']).dt.total_seconds() / 60

        # Categorize visitors
        single_page = (visitor_sessions['total_views'] == 1).sum()
        light_readers = (visitor_sessions['total_views'].between(2, 5)).sum()
        engaged_readers = (visitor_sessions['total_views'].between(6, 15)).sum()
        super_engaged = (visitor_sessions['total_views'] > 15).sum()

        total_visitors = len(visitor_sessions)

        print(f"\n👥 VISITOR ENGAGEMENT SEGMENTATION:")
        print(f"   Single Page Visitors: {single_page} ({single_page/total_visitors:.1%})")
        print(f"   Light Readers (2-5 views): {light_readers} ({light_readers/total_visitors:.1%})")
        print(f"   Engaged Readers (6-15 views): {engaged_readers} ({engaged_readers/total_visitors:.1%})")
        print(f"   Super Engaged (>15 views): {super_engaged} ({super_engaged/total_visitors:.1%})")

        # Insight on engagement
        engaged_ratio = (engaged_readers + super_engaged) / total_visitors
        if engaged_ratio > 0.25:
            self.insights.append(f"🔥 EXCEPTIONAL ENGAGEMENT: {engaged_ratio:.1%} of visitors are highly engaged (6+ views)")
            print(f"\n   🔍 INSIGHT: Your work creates deep engagement")
            print(f"      → Content quality is high enough to sustain multi-page sessions")
            print(f"      → Visitors are actively exploring, not just skimming")
            self.opportunities.append("CONTENT STRATEGY: Create 'reading paths' - suggest related papers to keep engaged readers exploring")

        # Bounce analysis
        bounce_rate = single_page / total_visitors
        if bounce_rate < 0.3:
            print(f"\n   ✓ LOW BOUNCE RATE: {bounce_rate:.1%} single-page visits is excellent")
            self.insights.append("✓ STRONG FIRST IMPRESSION: Low bounce rate indicates compelling initial content")
        elif bounce_rate > 0.5:
            print(f"\n   ⚠️ HIGH BOUNCE RATE: {bounce_rate:.1%} visitors leave after one page")
            self.risks.append("HIGH BOUNCE: Improve first-page hooks and internal linking to reduce single-page exits")

        # Session duration
        avg_duration = visitor_sessions[visitor_sessions['session_duration'] > 0]['session_duration'].mean()
        median_duration = visitor_sessions[visitor_sessions['session_duration'] > 0]['session_duration'].median()

        print(f"\n⏱️  SESSION DURATION:")
        print(f"   Average: {avg_duration:.1f} minutes")
        print(f"   Median: {median_duration:.1f} minutes")

        if avg_duration > 10:
            self.insights.append(f"⏰ DEEP READING SESSIONS: {avg_duration:.0f} min average suggests serious engagement, not casual browsing")
            print(f"\n   🔍 INSIGHT: Long sessions indicate scholarly reading, not skimming")

        # Multi-paper readers
        multi_paper = (visitor_sessions['unique_papers'] > 1).sum()
        print(f"\n📚 PAPER EXPLORATION:")
        print(f"   Visitors who read multiple papers: {multi_paper} ({multi_paper/total_visitors:.1%})")

        if multi_paper / total_visitors > 0.3:
            self.insights.append("📚 CROSS-PAPER INTEREST: Strong multi-paper exploration suggests thematic coherence in your work")
            self.opportunities.append("THEMATIC COLLECTIONS: Group related papers into collections/series for easier discovery")

        # Top engaged visitors
        top_visitors = visitor_sessions.nlargest(5, 'total_views')
        print(f"\n🌟 MOST ENGAGED VISITORS:")
        for idx, (visitor_id, row) in enumerate(top_visitors.iterrows(), 1):
            print(f"   {idx}. Visitor #{visitor_id}: {int(row['total_views'])} views, {row['unique_papers']:.0f} papers, {row['session_duration']:.0f} min")

        return self.insights

    def analyze_content_performance(self):
        """Analyze which content performs best and why"""
        print("\n" + "="*80)
        print("INSIGHT 3: CONTENT PERFORMANCE - What Resonates With Your Audience?")
        print("="*80)

        # Paper-level metrics
        paper_stats = self.df.groupby('Paper').agg({
            'Visitor ID': 'nunique',
            'URL': 'count',
            'Source': lambda x: x.value_counts().index[0] if len(x) > 0 else 'Unknown'
        })
        paper_stats.columns = ['unique_visitors', 'total_views', 'primary_source']
        paper_stats['engagement_ratio'] = paper_stats['total_views'] / paper_stats['unique_visitors']
        paper_stats = paper_stats.sort_values('unique_visitors', ascending=False)

        print(f"\n📊 PAPER PERFORMANCE:")
        # Exclude "Other Page" for more meaningful insights
        meaningful_papers = paper_stats[~paper_stats.index.isin(['Other Page'])]

        for paper, stats in meaningful_papers.head(10).iterrows():
            print(f"\n   {paper[:70]}")
            print(f"      Visitors: {stats['unique_visitors']:.0f} | Views: {stats['total_views']:.0f} | Engagement: {stats['engagement_ratio']:.2f}")
            print(f"      Primary Source: {stats['primary_source']}")

        # Engagement analysis
        high_engagement = meaningful_papers[meaningful_papers['engagement_ratio'] > 2.0]
        if len(high_engagement) > 0:
            print(f"\n   🔍 HIGH RE-READING: {len(high_engagement)} papers have >2x view-to-visitor ratio")
            self.insights.append("🔄 RE-READING BEHAVIOR: Some papers generate repeat views - likely reference material")
            self.opportunities.append("REFERENCE OPTIMIZATION: For high-engagement papers, add downloadable summaries or quick-reference guides")

        # Traffic source by paper
        print(f"\n🔗 TRAFFIC SOURCE EFFECTIVENESS:")
        source_performance = self.df.groupby('Source').agg({
            'Visitor ID': 'nunique',
            'Paper': lambda x: (x != 'Profile View').sum()  # Count paper views, not profile
        })
        source_performance.columns = ['visitors', 'paper_views']
        source_performance['paper_view_ratio'] = source_performance['paper_views'] / source_performance['visitors']
        source_performance = source_performance.sort_values('visitors', ascending=False)

        for source, stats in source_performance.head(8).iterrows():
            print(f"   {source:30s}: {stats['visitors']:4.0f} visitors → {stats['paper_view_ratio']:.2f} paper views/visitor")

        # Best converting sources
        best_sources = source_performance[source_performance['paper_view_ratio'] > 3]
        if len(best_sources) > 0:
            print(f"\n   🔍 HIGH-QUALITY SOURCES (>3 paper views/visitor):")
            for source in best_sources.index:
                print(f"      ✓ {source}")
            self.opportunities.append(f"DOUBLE DOWN: Focus promotion on {', '.join(best_sources.index.tolist())} - they bring engaged readers")

        return self.insights

    def analyze_geographic_opportunities(self):
        """Identify geographic expansion opportunities"""
        print("\n" + "="*80)
        print("INSIGHT 4: GEOGRAPHIC STRATEGY - Where Should You Expand?")
        print("="*80)

        # Continent-level analysis
        continent_stats = self.df.groupby('Continent').agg({
            'Visitor ID': 'nunique',
            'URL': 'count'
        })
        continent_stats.columns = ['visitors', 'views']
        continent_stats['views_per_visitor'] = continent_stats['views'] / continent_stats['visitors']
        continent_stats = continent_stats.sort_values('visitors', ascending=False)

        print(f"\n🌍 CONTINENTAL DISTRIBUTION:")
        for continent, stats in continent_stats.iterrows():
            print(f"   {continent:15s}: {stats['visitors']:4.0f} visitors | {stats['views']:5.0f} views | {stats['views_per_visitor']:.2f} views/visitor")

        # Identify opportunities
        print(f"\n🎯 GEOGRAPHIC OPPORTUNITIES:")

        # High engagement but low volume
        underrepresented = continent_stats[
            (continent_stats['views_per_visitor'] > continent_stats['views_per_visitor'].mean()) &
            (continent_stats['visitors'] < continent_stats['visitors'].quantile(0.5))
        ]

        if len(underrepresented) > 0:
            for continent in underrepresented.index:
                engagement = underrepresented.loc[continent, 'views_per_visitor']
                print(f"   🚀 {continent}: High engagement ({engagement:.1f} views/visitor) but low volume")
                print(f"      → Opportunity to expand reach through targeted outreach")
            self.opportunities.append(f"GEOGRAPHIC EXPANSION: Target {', '.join(underrepresented.index.tolist())} - high engagement indicates receptive audience")

        # Country deep dive for top continent
        top_continent = continent_stats.index[0]
        continent_countries = self.df[self.df['Continent'] == top_continent].groupby('Country')['Visitor ID'].nunique().sort_values(ascending=False)

        print(f"\n🏆 TOP COUNTRIES IN {top_continent.upper()}:")
        for country, visitors in continent_countries.head(5).items():
            print(f"   {country}: {visitors} visitors")

        # International vs domestic ratio
        us_visitors = self.df[self.df['IsUS']]['Visitor ID'].nunique()
        intl_visitors = self.df[~self.df['IsUS']]['Visitor ID'].nunique()
        total_visitors = us_visitors + intl_visitors

        print(f"\n🌎 DOMESTIC VS INTERNATIONAL:")
        print(f"   US Visitors: {us_visitors} ({us_visitors/total_visitors:.1%})")
        print(f"   International: {intl_visitors} ({intl_visitors/total_visitors:.1%})")

        if intl_visitors / total_visitors > 0.4:
            self.insights.append(f"🌐 STRONG INTERNATIONAL APPEAL: {intl_visitors/total_visitors:.0%} of audience is outside US")
            print(f"\n   🔍 INSIGHT: Your work has significant global reach")
            self.opportunities.append("INTERNATIONAL FOCUS: Consider translations, international conference submissions")

        return self.insights

    def analyze_visitor_journey_paths(self):
        """Analyze how visitors navigate through your content"""
        print("\n" + "="*80)
        print("INSIGHT 5: VISITOR JOURNEY - How Do People Discover & Navigate Your Work?")
        print("="*80)

        # Entry points
        entry_points = self.df.groupby('Visitor ID').first()['Paper'].value_counts()

        print(f"\n🚪 ENTRY POINTS (First page visitors see):")
        for i, (paper, count) in enumerate(entry_points.head(5).items(), 1):
            pct = count / len(entry_points) * 100
            print(f"   {i}. {paper[:60]:<60s}: {count:3d} visitors ({pct:5.1f}%)")

        # Profile to paper conversion
        profile_first = entry_points.get('Profile View', 0)
        profile_first_pct = profile_first / len(entry_points) * 100

        if profile_first_pct > 20:
            print(f"\n   🔍 INSIGHT: {profile_first_pct:.0f}% enter via your profile")
            print(f"      → Personal brand is strong - people seek YOU, not just your papers")
            self.insights.append("👤 PERSONAL BRAND STRENGTH: Many visitors start at your profile, not specific papers")
            self.opportunities.append("PROFILE OPTIMIZATION: Ensure profile clearly showcases your best/most relevant work")

        # Journey patterns - profile viewers who read papers
        profile_viewers = self.df[self.df['IsProfileView']]['Visitor ID'].unique()
        profile_to_paper = self.df[
            (self.df['Visitor ID'].isin(profile_viewers)) &
            (~self.df['IsProfileView'])
        ]['Visitor ID'].nunique()

        conversion_rate = profile_to_paper / len(profile_viewers) if len(profile_viewers) > 0 else 0

        print(f"\n📈 PROFILE-TO-PAPER CONVERSION:")
        print(f"   Profile Viewers: {len(profile_viewers)}")
        print(f"   Who Also Read Papers: {profile_to_paper} ({conversion_rate:.1%})")

        if conversion_rate > 0.7:
            self.insights.append("✓ EXCELLENT PROFILE CONVERSION: Most profile visitors continue to read your papers")
        elif conversion_rate < 0.4:
            self.risks.append("⚠️ LOW PROFILE CONVERSION: Profile visitors aren't continuing to papers - improve call-to-action")
            print(f"   ⚠️ Only {conversion_rate:.0%} of profile visitors read your papers")
            print(f"      → Improve profile layout, featured papers, or description")

        # Source to engagement correlation
        print(f"\n🔗 SOURCE QUALITY ANALYSIS:")
        source_engagement = self.df.groupby(['Source', 'Visitor ID']).size().reset_index(name='views')
        source_avg_engagement = source_engagement.groupby('Source')['views'].mean().sort_values(ascending=False)

        for source, avg_views in source_avg_engagement.head(7).items():
            print(f"   {source:30s}: {avg_views:.2f} avg views per visitor")

        # Identify best sources
        best_source = source_avg_engagement.index[0]
        best_engagement = source_avg_engagement.iloc[0]

        if best_engagement > 8:
            self.insights.append(f"🎯 {best_source} brings the most engaged visitors ({best_engagement:.1f} views/visitor)")
            self.opportunities.append(f"FOCUS PROMOTION: Prioritize {best_source} - it brings highly engaged readers")

        return self.insights

    def identify_growth_bottlenecks(self):
        """Identify what's preventing faster growth"""
        print("\n" + "="*80)
        print("INSIGHT 6: GROWTH BOTTLENECKS - What's Limiting Your Reach?")
        print("="*80)

        # Traffic source concentration
        source_visitors = self.df.groupby('Source')['Visitor ID'].nunique().sort_values(ascending=False)
        top_source_pct = source_visitors.iloc[0] / source_visitors.sum() * 100
        top_2_pct = source_visitors.iloc[:2].sum() / source_visitors.sum() * 100

        print(f"\n📊 TRAFFIC SOURCE CONCENTRATION:")
        print(f"   Top Source: {source_visitors.index[0]} = {top_source_pct:.1f}% of visitors")
        print(f"   Top 2 Sources: {top_2_pct:.1f}% of visitors")

        if top_source_pct > 40:
            self.risks.append(f"⚠️ OVER-RELIANCE ON {source_visitors.index[0]}: {top_source_pct:.0f}% of traffic from one source")
            print(f"\n   ⚠️ BOTTLENECK: Over-dependent on {source_visitors.index[0]}")
            print(f"      → Risk: Algorithm changes could devastate traffic")
            print(f"      → Action: Diversify traffic sources")

            # Suggest alternatives
            underutilized = ['Google', 'Twitter', 'LinkedIn', 'Academia Internal']
            current_sources = source_visitors.index.tolist()
            missing = [s for s in underutilized if s not in current_sources]
            weak = [s for s in underutilized if s in current_sources and source_visitors[s] < 20]

            if missing or weak:
                print(f"\n   💡 UNDERUTILIZED CHANNELS:")
                for channel in missing:
                    print(f"      ❌ {channel}: Not currently generating traffic")
                for channel in weak:
                    print(f"      📉 {channel}: Weak performance ({source_visitors[channel]} visitors)")

                self.opportunities.append(f"CHANNEL DIVERSIFICATION: Develop {', '.join(missing + weak)} presence")

        # Search visibility analysis
        google_visitors = source_visitors.get('Google', 0)
        total_visitors = source_visitors.sum()
        google_pct = google_visitors / total_visitors * 100

        print(f"\n🔍 SEARCH VISIBILITY:")
        print(f"   Google Traffic: {google_visitors} visitors ({google_pct:.1f}%)")

        if google_pct < 10:
            self.risks.append("📉 LOW SEARCH VISIBILITY: Weak Google presence limits organic discovery")
            print(f"\n   ⚠️ BOTTLENECK: Low search engine visibility")
            print(f"      → Your work isn't easily discoverable via Google")
            self.opportunities.append("SEO OPTIMIZATION: Improve paper titles, abstracts, keywords for search discoverability")
        elif google_pct > 30:
            self.insights.append("✓ STRONG SEO: Good search engine visibility driving organic traffic")

        # Content volume analysis
        unique_papers = self.df['Paper'].nunique()
        views_per_paper = len(self.df) / unique_papers

        print(f"\n📚 CONTENT PORTFOLIO:")
        print(f"   Unique Papers/Pages: {unique_papers}")
        print(f"   Average Views per Paper: {views_per_paper:.0f}")

        if unique_papers < 5:
            self.risks.append("📉 LIMITED CONTENT: Small portfolio limits discovery opportunities")
            print(f"\n   ⚠️ BOTTLENECK: Limited content portfolio")
            print(f"      → Few papers means fewer entry points for discovery")
            self.opportunities.append("CONTENT CREATION: Publish more papers to increase discovery surface area")

        # Temporal consistency
        daily_active_days = self.df.groupby('Date').size()
        days_in_period = (self.df['Time'].max() - self.df['Time'].min()).days
        active_days = len(daily_active_days)
        consistency = active_days / days_in_period

        print(f"\n📅 TRAFFIC CONSISTENCY:")
        print(f"   Days with Traffic: {active_days} out of {days_in_period} ({consistency:.1%})")

        if consistency < 0.3:
            self.risks.append("📉 SPORADIC TRAFFIC: Inconsistent visitor flow suggests limited ongoing discovery")
            print(f"\n   ⚠️ BOTTLENECK: Sporadic traffic pattern")
            print(f"      → Need more consistent promotion or evergreen content")
            self.opportunities.append("CONSISTENT PROMOTION: Establish regular sharing schedule to maintain visibility")

        return self.risks

    def generate_strategic_recommendations(self):
        """Generate prioritized strategic recommendations"""
        print("\n" + "="*80)
        print("STRATEGIC RECOMMENDATIONS - Your Action Plan")
        print("="*80)

        print(f"\n✅ KEY STRENGTHS TO LEVERAGE:")
        for i, insight in enumerate([i for i in self.insights if '✓' in i or '🔥' in i], 1):
            print(f"   {i}. {insight}")

        print(f"\n⚠️  RISKS TO MITIGATE:")
        for i, risk in enumerate(self.risks, 1):
            print(f"   {i}. {risk}")

        print(f"\n🚀 TOP GROWTH OPPORTUNITIES:")
        # Prioritize opportunities
        for i, opp in enumerate(self.opportunities[:10], 1):
            print(f"   {i}. {opp}")

        # Create action priorities
        print(f"\n🎯 IMMEDIATE ACTION PRIORITIES (Next 30 Days):")

        priorities = []

        # Priority 1: Address biggest risk
        if self.risks:
            priorities.append(("CRITICAL", self.risks[0]))

        # Priority 2: Leverage biggest strength
        if self.opportunities:
            priorities.append(("HIGH", self.opportunities[0]))

        # Priority 3: Diversification
        if any('DIVERSIF' in o.upper() for o in self.opportunities):
            div_opp = [o for o in self.opportunities if 'DIVERSIF' in o.upper()][0]
            priorities.append(("HIGH", div_opp))

        # Priority 4: Content optimization
        if any('CONTENT' in o.upper() or 'SEO' in o.upper() for o in self.opportunities):
            content_opp = [o for o in self.opportunities if 'CONTENT' in o.upper() or 'SEO' in o.upper()][0]
            priorities.append(("MEDIUM", content_opp))

        for i, (priority, action) in enumerate(priorities[:5], 1):
            print(f"   {i}. [{priority}] {action}")

        return {
            'insights': self.insights,
            'opportunities': self.opportunities,
            'risks': self.risks,
            'priorities': priorities
        }

    def run_deep_analysis(self):
        """Execute complete deep insights analysis"""
        print("\n" + "="*80)
        print("ACADEMIA.EDU DEEP INSIGHTS ENGINE")
        print("Strategic Intelligence for Academic Impact")
        print("="*80)

        self.analyze_temporal_patterns()
        self.analyze_visitor_behavior()
        self.analyze_content_performance()
        self.analyze_geographic_opportunities()
        self.analyze_visitor_journey_paths()
        self.identify_growth_bottlenecks()
        recommendations = self.generate_strategic_recommendations()

        # Save detailed report
        output = {
            'insights': self.insights,
            'opportunities': self.opportunities,
            'risks': self.risks,
            'recommendations': recommendations,
            'generated_at': datetime.now().isoformat()
        }

        output_path = '/home/xluxx/pablo_context/academia_strategic_insights.json'
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(output, f, indent=2, ensure_ascii=False)

        print(f"\n💾 Strategic insights saved to: {output_path}")

        print("\n" + "="*80)
        print("DEEP INSIGHTS ANALYSIS COMPLETE")
        print("="*80)


def main():
    csv_path = '/home/xluxx/pablo_context/Academia.csv'
    analyzer = DeepInsightsAnalyzer(csv_path)
    analyzer.run_deep_analysis()


if __name__ == "__main__":
    main()
