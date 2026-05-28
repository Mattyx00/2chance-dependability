package controller;

import model.beans.Carrello;
import model.beans.Prodotto;
import model.beans.ProdottoCarrello;
import model.beans.Utente;

import javax.servlet.*;
import javax.servlet.annotation.WebFilter;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpSession;
import java.io.IOException;

@WebFilter(filterName = "SessionInjectionFilter", urlPatterns = "/*")
public class SessionInjectionFilter implements Filter {

    private boolean testMode = false;

    @Override
    public void init(FilterConfig filterConfig) throws ServletException {
        String envTestMode = System.getenv("ECO_TEST_MODE");
        if ("true".equalsIgnoreCase(envTestMode)) {
            testMode = true;
        }
    }

    @Override
    public void doFilter(ServletRequest request, ServletResponse response, FilterChain chain)
            throws IOException, ServletException {
        if (testMode && request instanceof HttpServletRequest) {
            HttpServletRequest httpRequest = (HttpServletRequest) request;
            HttpSession session = httpRequest.getSession();

            // Inject mock user if not present
            if (session.getAttribute("user") == null) {
                Utente mockUser = new Utente();
                mockUser.setId(999);
                mockUser.setNome("EcoTest");
                mockUser.setCognome("User");
                mockUser.setEmail("ecotest@example.com");
                mockUser.setTelefono("1234567890");
                mockUser.setImmagine("logo.png"); // to prevent any missing image issues in profile page
                mockUser.setAdmin(true); // make them admin to bypass admin checks on dashboard
                session.setAttribute("user", mockUser);
            }

            // Inject mock carrello if not present, and populate with a mock product
            if (session.getAttribute("carrello") == null) {
                Carrello mockCart = new Carrello();
                
                Prodotto mockProduct = new Prodotto();
                mockProduct.setId(100);
                mockProduct.setMarca("Generic");
                mockProduct.setModello("Heavy Item");
                mockProduct.setPrezzo(199.99);
                mockProduct.setPeso(2.5);
                mockProduct.setImmagine("logo.png");
                mockProduct.setQuantitaProdotto(10);
                mockProduct.setDescrizione("This is a mock description for testing.");
                
                ProdottoCarrello item = new ProdottoCarrello(mockProduct, 1);
                mockCart.aggiungiProdotto(item);
                
                session.setAttribute("carrello", mockCart);
            }
        }
        chain.doFilter(request, response);
    }

    @Override
    public void destroy() {
    }
}
