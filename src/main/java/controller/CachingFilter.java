package controller;

import javax.servlet.*;
import javax.servlet.annotation.WebFilter;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import java.io.IOException;

@WebFilter(filterName = "CachingFilter", urlPatterns = "/*")
public class CachingFilter implements Filter {

    private static final long MAX_AGE_SECONDS = 604800L; // 1 week

    @Override
    public void init(FilterConfig filterConfig) throws ServletException {
    }

    @Override
    public void doFilter(ServletRequest request, ServletResponse response, FilterChain chain)
            throws IOException, ServletException {
        
        HttpServletRequest httpRequest = (HttpServletRequest) request;
        HttpServletResponse httpResponse = (HttpServletResponse) response;
        String requestURI = httpRequest.getRequestURI();

        // Check if request is for static resources
        if (isStaticResource(requestURI)) {
            // Set Cache-Control: public, max-age=604800
            httpResponse.setHeader("Cache-Control", "public, max-age=" + MAX_AGE_SECONDS);
            // Set Expires header
            httpResponse.setDateHeader("Expires", System.currentTimeMillis() + (MAX_AGE_SECONDS * 1000L));
            // Add CORS header for anonymous crossorigin requests
            httpResponse.setHeader("Access-Control-Allow-Origin", "*");
        }

        chain.doFilter(request, response);
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
