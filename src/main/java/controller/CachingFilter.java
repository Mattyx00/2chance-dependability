package controller;

import javax.servlet.*;
import javax.servlet.annotation.WebFilter;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpServletResponseWrapper;
import java.io.IOException;

@WebFilter(filterName = "CachingFilter", urlPatterns = "/*")
public class CachingFilter implements Filter {

    private static final long MAX_AGE_SECONDS = 604800L; // 1 week

    private static class CacheControlResponseWrapper extends HttpServletResponseWrapper {
        private final long maxAge;

        public CacheControlResponseWrapper(HttpServletResponse response, long maxAge) {
            super(response);
            this.maxAge = maxAge;
        }

        @Override
        public void setHeader(String name, String value) {
            if ("Cache-Control".equalsIgnoreCase(name)) {
                super.setHeader(name, "public, max-age=" + maxAge);
            } else {
                super.setHeader(name, value);
            }
        }

        @Override
        public void addHeader(String name, String value) {
            if ("Cache-Control".equalsIgnoreCase(name)) {
                super.setHeader(name, "public, max-age=" + maxAge);
            } else {
                super.addHeader(name, value);
            }
        }
    }

    @Override
    public void init(FilterConfig filterConfig) throws ServletException {
    }

    @Override
    public void doFilter(ServletRequest request, ServletResponse response, FilterChain chain)
            throws IOException, ServletException {
        
        HttpServletRequest httpRequest = (HttpServletRequest) request;
        HttpServletResponse httpResponse = (HttpServletResponse) response;
        String requestURI = httpRequest.getRequestURI();

        if (isStaticResource(requestURI)) {
            CacheControlResponseWrapper wrappedResponse = new CacheControlResponseWrapper(httpResponse, MAX_AGE_SECONDS);
            wrappedResponse.setHeader("Cache-Control", "public, max-age=" + MAX_AGE_SECONDS);
            wrappedResponse.setDateHeader("Expires", System.currentTimeMillis() + (MAX_AGE_SECONDS * 1000L));
            wrappedResponse.setHeader("Access-Control-Allow-Origin", "*");
            chain.doFilter(request, wrappedResponse);
        } else {
            chain.doFilter(request, response);
        }
    }

    @Override
    public void destroy() {
    }

    private boolean isStaticResource(String uri) {
        String lower = uri.toLowerCase();
        return lower.endsWith(".css") || 
               lower.endsWith(".js") || 
               lower.endsWith(".png") || 
               lower.endsWith(".jpg") || 
               lower.endsWith(".jpeg") || 
               lower.endsWith(".webp") || 
               lower.endsWith(".avif") || 
               lower.endsWith(".gif") || 
               lower.endsWith(".otf") || 
               lower.endsWith(".woff") || 
               lower.endsWith(".woff2") || 
               lower.endsWith(".ttf") ||
               lower.endsWith(".ico");
    }
}
